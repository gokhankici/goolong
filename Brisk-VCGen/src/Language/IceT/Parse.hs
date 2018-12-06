{-# LANGUAGE ParallelListComp #-}
module Language.IceT.Parse where
import Language.IceT.Types
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token


{-
Core languange:
---------------
 prog(ds, t)         : declarations ds, trace t
 decl(x, s)          : declare x, sort s

 int                 : sorts
 map(s, s)           :
 set                 :

 par([A,B,C])        : A || B || C.
 seq([A,B,C])        : A; B; C.
 skip                : no-operation.
 send(p, x, v)       : process p sends value v to
  | x=e_pid(q)       :       - process q.
  | x=e_var(y)       :       - the pid stored in variable y.
 send(p, x, type, v)  : send a message of type "type".
 recv(p, v)          : process p receives value v.
 recv(p, x, v)       : process p receives value v from
  | x=e_pid(q)       :       - process q.
  | x=e_var(y)       :       - the pid stored in variable y.
  | x=type(t)        :       - of type t.
 recv(p, x, type, v) : receive messages of type "type", only.
 sym(P, S, A)        : composition of symmetric processes p in set s with source A.
                       s must be distinct from process ids.
 for(m, P, S, A)     : process m executes A for each process p in s.
 iter(p, k, A)       : process p executes A k-times.
 while(p, cond, A)   : process p executes A while cond is true.
 nondet(P, s, A)        : process P is chosen non-deterministically in A.
 assign(p, x, v)     : process p assigns value v to variable x.
 ite(P, Cond, A, B)  : process p executes A if Cond holds and B, otherwise.
 if(P, Cond, A)      : Short for ite(P, Cond, A, skip).
 pair(x, y)          : pair of values x and y.
 cases(p, x, C, d)   : proccess p performs a case switch on x with cases specified in
 | C=case(p, exp, A) : C and default case d.
 seq([x,y,z])
-}  

{-> parseString "for(P, X, bs, seq([assign(X,v,0),skip]))"
-}

type ParsedAnnot = Id  
type ParsedProgram = Program ParsedAnnot

parseFile :: String -> IO ParsedProgram
parseFile file
  = readFile file >>= return . parseString

parseString :: String -> ParsedProgram
parseString str
  = case parse iceTParser "" str of
      Left e  -> error $ show e
      Right r -> r

iceTParser :: Parser ParsedProgram  
iceTParser = whiteSpace >> program

program :: Parser ParsedProgram
program = do reserved "prog"  
             p <- parens $ do
               _     <- ident
               comma
               decls <- list (fmap B decl <|> fmap C declCard)
               comma
               p     <- functor "ensures" prop
               comma
               t     <- stmt
               let vars  = [ v | B v <- decls ]
                   cards = [ k | C k <- decls ]
               return Prog { decls     = vars
                           , cardDecls = cards
                           , ensures   = p
                           , prog      = t
                           }
             dot
             return p
  where
    tryCards = try (comma >> list declCard) <|> return []

data ParsedDecl a = B Binder | C (Card a)

decl :: Parser Binder
decl = do reserved "decl"
          parens $ do
            v <- ident
            comma
            s <- sort
            return $ Bind v s

declCard :: Parser (Card a)
declCard = functor "decl_card" $ do
  nm    <- ident
  comma
  owner <- ident
  comma
  i     <- ident
  comma
  e     <- ident
  comma
  p     <- prop
  return $ Card nm owner i e p

sort :: Parser Sort
sort = int <|> set <|> array

int, set, array :: Parser Sort
int   = reserved "int"    >> return Int
set   = reserved "set"    >> return Set
array = do reserved "map"
           parens $ do
             t1 <- index
             comma
             t2 <- sort
             return $ Map t1 t2

index :: Parser Index
index = (reserved "int" >> return IntIdx)
    <|> (reserved "set" >> parens ident >>= return . SetIdx)
            

stmt :: Parser (Stmt ParsedAnnot)
stmt =  skip
    <|> assignment
    <|> seqs
    <|> cases
    <|> ite
    <|> foreach
    <|> iter
    <|> while
    <|> par
    <|> atomic
    <|> havoc
    <|> pre <|> assert <|> assume

havoc = functor "havoc" $ do
  p <- ident
  comma
  x <- ident
  return (Assign p (Bind x Int) p NonDetValue p)

pre        = do (Assert p _ w) <- functor "pre" $ assertBody
                return (Assert p True w)
assume     = functor "assume" $ do
  w <- ident
  comma
  p <- prop <?> "prop"
  return (Assume p w)
assert     = functor "assert" $ assertBody
assertBody = do w <- ident
                comma
                p <- prop <?> "prop"
                return (Assert p False w)
  

par = functor "sym" $ do
  p <- ident
  comma
  ps <- ident
  comma
  s <- stmt
  return (Par p ps TT s "")

atomic = do s <- functor "atomic" $ stmt
            return (Atomic s "")

skip, assignment, seqs, cases, foreach, while :: Parser (Stmt ParsedAnnot)
skip = reserved "skip" >> return (Skip "")

assignment = functor "assign" (try assignVars <|> assignConst)

assignVars, assignConst :: Parser (Stmt ParsedAnnot)
assignConst = do
  p <- ident
  comma
  xs <- assignLHS
  comma
  es <- assignRHS
  matchAssign p p xs es
  
assignVars = do 
    p <- ident
    comma
    xs <- assignLHS
    comma
    q <- ident
    comma
    ys <- assignRHS
    matchAssign p q xs ys

matchAssign p q [i] [e]
  = return $ Assign p (Bind i Int) q e p
matchAssign p q is es
  | length is == length es
  = return $ Seq ([Assign p (Bind i Int) q e p | i <- is | e <- es]) p
assignLHS = pairNested ident 
assignRHS = pairNested expr

pairNested p
  = one <|> pair
  where one  = do { i <- p; return [i] }
        pair = functor "pair" $ do
          i1 <- (pairNested p)
          comma
          i2 <- (pairNested p)
          return (i1 ++ i2)


seqs = do reserved "seq"
          stmts <- parens $ list stmt
          case stmts of
            [s] -> return s
            _   -> return $ Seq stmts ""

ite = functor "ite" $ do
  p <- ident
  comma
  test <- prop
  comma
  s1 <- stmt
  comma
  s2 <- stmt
  return $ If test s1 s2 p

cases = functor "cases" $ do
  p <- ident
  comma
  discr <- expr
  comma
  cs <- list casestmt
  comma
  stmt
  return $ Cases discr cs p

casestmt = functor "case" $ do
  p <- ident
  comma
  e <- expr
  comma
  s <- stmt
  return $ Case e s p

foreach = functor "for" $ do
  who <- ident
  comma
  x   <- ident
  comma
  xs  <- ident
  comma
  rest <- ident
  comma
  inv  <- prop
  comma
  s   <- stmt
  return $ ForEach (Bind x Int)
                   (Bind xs Set)
                   (rest, inv)
                   s
                   who
iter = functor "iter" $ do
  k <- ident
  comma
  inv <- prop
  comma
  s <- stmt
  return $ ForEach (Bind "!iter" Int)
                   (Bind k Set)
                   ("!i", inv)
                   s
                   ""
  
prop = (reserved "true"  >> return TT)
   <|> (reserved "false" >> return FF)
   <|> (reserved "ndet" >> return NonDetProp)
   <|> atom
   <|> implies
   <|> andProp
   <|> orProp
   <|> notProp
   <|> forallProp
   <|> existsProp
   <|> elemProp
   <|> hereProp
   <|> doneProp
   
doneProp = functor "done" $ do
  p <- ident
  comma
  ps <- ident
  return $ Atom Eq (pc ps p) (Const (-1))
atom = do e1 <- expr
          r  <- rel
          e2 <- expr
          return $ Atom r e1 e2

rel =  try (reservedOp "=<"  >> return Le)
   <|> (reservedOp "<"  >> return Lt)
   <|> (reservedOp ">"  >> return Gt)
   <|> (reservedOp "=" >> return Eq)

forallProp = functor "forall" $ do
  ds <- list decl
  comma
  p <- prop
  return $ Forall ds p
existsProp = functor "exists" $ do
  ds <- list decl
  comma
  p <- prop
  return $ Exists ds p

implies = functor "implies" $ do
  p1 <- prop
  comma
  p2 <- prop
  return (p1 :=>: p2)

andProp = functor "and" $ do
  ps <- list prop
  return $ And ps

orProp = functor "or" $ do
  ps <- list prop
  return $ Or ps

notProp = functor "not" $ (Not <$> prop)

elemProp = functor "elem" $ do
  e1 <- expr
  comma
  e2 <- expr
  return $ Atom SetMem e1 e2

hereProp = functor "here" $ (Here <$> expr)

while = do reserved "While"
           parens $ do
             who <- ident
             comma
             (Var x) <- expr
             comma
             s <- stmt
             return $ While x s who

-- expr = num <|> var <|> sel <|> sel' <|> ndet <|> binexpr

expr = buildExpressionParser table term <?> "expression"
  where
    table = [ [ Infix (reservedOp "*" >> return (Bin Mul)) AssocLeft
              , Infix (reservedOp "/" >> return (Bin Div)) AssocLeft
              ]
            , [ Infix (reservedOp "+" >> return (Bin Plus)) AssocLeft
              , Infix (reservedOp "-" >> return (Bin Minus)) AssocLeft
              ]
            ]
    term  = num <|> var <|> sel <|> set_add <|> size <|> upd <|> ndet <?> "term" 

num = do i <- integer
         return $ Const (fromInteger i)
var = do i <- ident
         return $ Var i
sel = functor "sel" sel'
  <|> functor "ref" sel'
  <|> do {Select e1 e2 <- functor "varOf" sel'; return (Select e2 e1)}
  where
   sel' = do
     e1 <- expr
     comma
     e2 <- expr
     return (Select e1 e2)

set_add = functor "set_add" $ do
  e1 <- expr
  comma
  e2 <- expr
  return (Bin SetAdd e1 e2)

size = functor "card" $ do
  e <- expr
  return (Size e)

upd = functor "upd" $ do
  Store <$> expr <*> (comma >> expr) <*> (comma >> expr)

ndet = reserved "ndet" >> return NonDetValue

op = symbol "+" >> return Plus


list p = brackets $ commaSep p
functor f p = reserved f >> parens p

lexer      = Token.makeTokenParser languageDef
ident      = Token.identifier lexer
reserved   = Token.reserved lexer
integer    = Token.integer lexer
comma      = Token.comma lexer
dot        = Token.dot lexer
whiteSpace = Token.whiteSpace lexer
parens     = Token.parens lexer
brackets   = Token.brackets lexer
commaSep   = Token.commaSep lexer
symbol     = Token.symbol lexer
reservedOp = Token.reservedOp lexer

languageDef =
  emptyDef { Token.identStart    = letter <|> char '_'
           , Token.identLetter   = alphaNum <|> char '_'
           , Token.reservedNames = [ "par"
                                   , "seq"
                                   , "skip"
                                   , "for"
                                   , "iter"
                                   , "while"
                                   , "nondet"
                                   , "ndet"
                                   , "assign"
                                   , "cases"
                                   , "ite"
                                   , "if"
                                   , "case"
                                   , "skip"
                                   , "prog"
                                   , "int"
                                   , "decl"
                                   , "map"
                                   , "true"
                                   , "false"
                                   , "implies"
                                   , "forall"
                                   , "exists"
                                   , "and"
                                   , "or"
                                   , "not"
                                   , "elem"
                                   , "sel"
                                   , "upd"
                                   , "ref"
                                   , "ensures"
                                   , "sym"
                                   , "atomic"
                                   , "done"
                                   , "pair"
                                   , "assert"
                                   , "assume"
                                   , "here"
                                   , "varOf"
                                   , "havoc"
                                   , "card"
                                   , "decl_card"
                                   ]
           , Token.commentStart = "/*"
           , Token.commentEnd   = "*/"
           , Token.commentLine  = "//"
           , Token.reservedOpNames = [ "-", "+", "<", "=<", "/", "=", ">" ]
           }
