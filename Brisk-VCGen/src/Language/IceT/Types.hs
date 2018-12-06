{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}
module Language.IceT.Types where
import Prelude hiding (and, or)
import Control.Monad.State
import Data.Map.Strict as M hiding (foldl')
import Data.List as L hiding (and, or)
import Text.Printf

import Debug.Trace
dbg :: Show a => String -> a -> a
dbg msg x = trace (printf "[%s]: %s\n" msg (show x)) x

-------------------------------------------------------------------------------
-- Programs
-------------------------------------------------------------------------------
type VCAnnot a = (Show a, Process a)

class Process a where
  process :: a -> Id

instance Process Id where
  process = id

type Id = String

data Program a = Prog { decls     :: [Binder]
                      , cardDecls :: [Card a]
                      , prog      :: Stmt a
                      , ensures   :: Prop a
                      }  
  deriving (Show)

data Card a = Card { cardName :: Id
                   , cardOwner :: Id
                   , cardId :: Id
                   , cardElem :: Id
                   , cardProp :: Prop a
                   }
  deriving (Show)

data Stmt a = Skip a
            | Par Id Id (Prop a) (Stmt a) a
            | Assign Id Binder Id (Expr a) a
            | Seq [Stmt a] a
            | Atomic (Stmt a) a
            | Assume (Prop a) a
            | Assert (Prop a) Bool a
            | If (Prop a) (Stmt a) (Stmt a) a
            | Cases (Expr a) [Case a] a
            | ForEach Binder Binder (Id, Prop a) (Stmt a) a
            | While Id (Stmt a) a
            deriving (Eq, Show, Functor, Foldable, Traversable)

data Case a = Case { caseGuard :: Expr a
                   , caseStmt  :: Stmt a
                   , caseAnnot :: a
                   }
  deriving (Eq, Show, Functor, Foldable, Traversable)
            
data Expr a = Const Int
            | EmptySet
            | NonDetValue
            | Var Id
            | PExpr (Prop a)
            | Select (Expr a) (Expr a)
            | Store (Expr a) (Expr a) (Expr a)
            | Size (Expr a)
            | Ite (Prop a) (Expr a) (Expr a)
            | Bin Op (Expr a) (Expr a)
  deriving (Eq, Show, Functor, Foldable, Traversable)

data Op     = Plus
            | Minus
            | Mul
            | Div
            | SetSubSingle -- Xs - {x}
            | SetAdd
  deriving (Eq, Show)

data Prop a = TT
            | FF
            | Atom Rel (Expr a) (Expr a)
            | Not (Prop a)
            | And [Prop a]
            | Or [Prop a]
            | Prop a :=>: Prop a
            | Forall [Binder] (Prop a)
            | Exists [Binder] (Prop a)
            | Here (Expr a)
            | Prop (Expr a)
            | PVar Id
            | NonDetProp
            | Let [(Binder, Expr a)] (Prop a)
            deriving (Eq, Show, Functor, Foldable, Traversable)
data Binder = Bind { bvar :: Id, bsort :: Sort }
  deriving (Eq, Show)
data Sort = Int | Set | Map Index Sort | Bool
  deriving (Eq, Show)
data Index = SetIdx Id
           | IntIdx
  deriving (Eq, Show)

data Rel = Eq | Le | Lt | Gt | SetMem
  deriving (Eq, Show)

pc :: Id -> Id -> Expr a
pc ps p = Select (Var (pcName ps)) (Var p)

pcName :: Id -> Id
pcName ps = "pc!" ++ ps
  

writes :: Stmt a -> [Binder]
writes = nub . go
  where
    go (Skip _)           = []
    go (If _ s1 s2 _)     = go s1 ++ go s2
    go (Atomic s _)       = go s
    go (Assign _ x _ _ _) = [x]
    go (Seq stmts _)      = stmts >>= go
    go (ForEach x _ _ s _)= x : go s
    go (While _ s _)      = go s
    go (Cases _ cs _)     = cs >>= go . caseStmt
    go (Par _ _ _ s _)    = go s
    go (Assert _ _ _)     = []
    go (Assume _ _ )      = []
-------------------------------------------------------------------------------
-- Actions
-------------------------------------------------------------------------------
-- Action: scope - (p, ps) - path - loc - exits - stmt
data Action a = Action [Binder] [(Id, Id)] [Prop a] Int [(Prop a, Int)] (Stmt a)
  deriving (Show, Eq, Functor)

ins :: Int -> Prop a -> Maybe [(Prop a, Int)] -> Maybe [(Prop a, Int)]
ins v g Nothing   = Just [(g,v)]
ins v g (Just vs) = Just ((g,v):vs)

label :: Stmt a -> Stmt (a, Int)
label s = evalState (mapM go s) 0
  where
    go :: s -> State Int (s, Int)
    go s = do i <- get :: State Int Int
              put (i + 1)
              return (s, i)

firstOf :: VCAnnot a => Stmt (a, Int) -> [Int]
firstOf (Skip _)
  = []
firstOf (Assign _ _ _ _ (_,i))
  = [i]
firstOf (Atomic s (_,i))
  = [i]
firstOf (Seq (s:ss) _)
  = firstOf s
firstOf (ForEach _ _ _ s _)
  = firstOf s
firstOf (If _ s1 s2 _)
  = firstOf s1 ++ firstOf s2
firstOf s
  = error ("firstOf: " ++ show s)

data CFG a = CFG { path  :: [Prop a]
                 , binds :: [Binder]
                 , m     :: M.Map Int [(Prop a, Int)]
                 , us    :: M.Map Id Id
                 }  
type CfgM s a = State (CFG s) a

updCfg m s outs
  = foldl' (\m o ->
              foldl' (\m i ->
                        M.alter (ins i TT) o m) m (firstOf s)) m outs
  
toActions :: VCAnnot a => Id -> Stmt (a, Int) -> CfgM (a, Int) ([Int], [Action (a, Int)])
toActions w (Atomic s (_, i))
  = do p  <- gets path
       bs <- gets binds
       us <- M.toList <$> gets us
       return ([i], [Action bs us p i [] s])
toActions w s@(Assign _ _ _ _ l)
  = toActions w (Atomic s l)
toActions w (Skip _)
  = return ([], [])
toActions w (ForEach x xs (r, i) s (l,_))
  = pushForLoop w (process l) x xs $ do
       (outs, as) <- toActions w s
       modify $ \st -> st { m = updCfg (m st) s outs }
       return (outs, as)
toActions w (Seq ss _) = do (last, as) <- foldM go ([], []) ss
                            return (last, concat as)
  where
    go (prev, s0) s = do (out, s') <- toActions w s
                         modify $ \st -> st { m = updCfg (m st) s prev }
                         return (out, s':s0)
toActions w (If p s1 s2 l)
  = do p0          <- gets path
       modify $ \s -> s { path = p : p0 }
       (last, a1)  <- toActions w s1
       modify $ \s -> s { path = Not p : p0 }
       (last', a2) <- toActions w s2
       modify $ \s -> s { path = p0 }
       return (last ++ last', a1 ++ a2)
toActions w s = error ("buildCFG\n" ++ show s)

pushForLoop :: Id -> Id -> Binder -> Binder -> CfgM s a -> CfgM s a
pushForLoop p q x xs act
  = withUnfold (bvar x) (bvar xs) $ do
       vs0 <- gets binds
       p0  <- gets path
       modify $ \s -> s { binds = x : vs0
                        , path  = grd : p0
                        }
       r  <- act
       modify $ \s -> s { binds = vs0, path = p0 }
       return r 
  where
    grd | p == q    = Atom SetMem (Var (bvar x)) (Var $ bvar xs) 
        | otherwise = Atom SetMem (Var $ bvar x) (Var $ bvar xs)
    sel x p = Select (Var (bvar x)) (Var p)

assgn :: Id -> Id -> Stmt ()
assgn x y = Atomic (Assign "" (Bind x Int) "" (Var y) ()) ()

actions :: VCAnnot a => Id -> Stmt a -> [Binder] -> ([Int], [Action a], [Int])
actions w s bs
  = (firstOf si, [ Action bs un ps i (getOuts i) s | Action bs un ps i _ s <- as0 ], outs)
  where
     cfg        = m st
     st0        = CFG [] (Bind w Int : bs) M.empty M.empty
     as0        = fmap (fmap fst) as
     si         = label s
     ((outs,as), st) = runState (toActions w si) st0  
     getOuts i       = [ (fst <$> p, i) | (p, i) <- M.findWithDefault [] i cfg ]

exitNodes :: M.Map Int [(Prop (a, Int), Int)] -> [Int]
exitNodes m = [ i | i <- outs, i `notElem` ins ]
  where
    ins  = M.keys m
    outs = nub $ M.foldr' (\outs0 outs -> outs ++ (snd <$> outs0)) [] m

withUnfold :: Id -> Id -> CfgM s a -> CfgM s a
withUnfold p ps act
  = do us0 <- gets us
       modify $ \s -> s { us = M.insert p ps (us s)  }
       r <- act
       modify $ \s -> s { us = us0}
       return r
  
cfg p s = m . snd $ runState (toActions p s) (CFG [] [] M.empty M.empty)
-------------------------------------------------------------------------------
-- Formulas
-------------------------------------------------------------------------------
and :: [Prop a] -> Prop a
and ps  = case compact TT ps of
            []  -> TT
            [p] -> p
            ps'  -> And ps'
or ps = case compact FF ps of
          [] -> FF
          [p] -> p
          ps' -> Or ps'
compact one ps = L.filter (/= one) (simplify <$> ps)
simplify (p :=>: TT) = TT
simplify (TT :=>: p) = p
simplify (And ps)    = and ps
simplify (Or ps)     = or  ps
simplify p           = p

class Subst b where
  subst :: Id -> (Expr a) -> b a -> b a

instance Subst Stmt where
  subst x a (Assign p y q e l)
    = Assign p y q (subst x a e) l
  subst x a (Seq stmts l)
    = Seq (subst x a <$> stmts) l
  subst x a for@(ForEach y xs inv s l)
    | x /= bvar y = ForEach y xs (subst x a <$> inv) (subst x a s) l
    | otherwise   = for
  subst x a (Atomic s l)
    = Atomic (subst x a s) l
  subst x a (If p s1 s2 l)
    = If (subst x a p) (subst x a s1) (subst x a s2) l
  subst x a (Assert p b l)
    = Assert (subst x a p) b l
  subst _ _ (Skip l)
    = Skip l
  subst x a (Assume p l)
    = Assume (subst x a p) l
  subst x a (Par p ps i s l)
    = Par p ps i (subst x a s) l
  subst x a _
    = error "subst stmt"
  

instance Subst Expr where
  subst _ _ (Const i)
    = Const i
  subst x e v@(Var y)
    | x == y    = e
    | otherwise = v
  subst x e (Bin o e1 e2)
    = Bin o (subst x e e1) (subst x e e2)
  subst x e (Select e1 e2)
    = Select (subst x e e1) (subst x e e2)
  subst x e (Store e1 e2 e3)
    = Store (subst x e e1) (subst x e e2) (subst x e e3)
  subst _ _ EmptySet
    = EmptySet
  subst x e (Size a)
    = Size (subst x e a)
  subst _ _ NonDetValue
    = NonDetValue
  subst x e (PExpr a)
    = PExpr $ subst x e a

instance Subst Prop where
  subst x e                 = go
    where go (Atom r e1 e2) = Atom r (subst x e e1) (subst x e e2)
          go (Not p)        = Not (subst x e p)
          go (And ps)       = And (go <$> ps)
          go (Or ps)        = Or (go <$> ps)
          go (p :=>: q)     = go p :=>: go q
          go (Forall xs p)
            | x `elem` (bvar <$> xs)
            = Forall xs p
            | otherwise
            = Forall xs (go p)
          go (Exists xs p)
            | x `elem` (bvar <$> xs)
            = Exists xs p
            | otherwise
            = Exists xs (go p)
          go TT             = TT
          go FF             = FF
          go (Prop e')      = Prop (subst x e e')
          go (Here e')      = Here $ subst x e e'
          go (NonDetProp)   = NonDetProp
          go (Let xs p)
            | x `elem` (bvar . fst <$> xs) = Let xs p
            | otherwise                    = Let xs (go p)
