{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}
module Language.IceT.VCGen (verifyFile, verifyProgram) where
import Prelude hiding (and, or)
import Language.IceT.Types
import Language.IceT.SMT
import Language.IceT.Pretty (pp, render)
import Language.IceT.Parse (parseFile, parseString)

import Control.Monad.State
import Data.List hiding (and, or)
import qualified Data.Map.Strict as M
import Text.PrettyPrint.HughesPJ
import Text.Printf
import System.Exit
import System.Process
import GHC.IO.Handle

import Debug.Trace
dbgPP msg x = trace (printf "[%s]: %s\n" msg (show (pp x))) x
-------------------------------------------------------------------------------
-- IO one-stop-shop
-------------------------------------------------------------------------------
verifyProgram :: String -> IO Bool
verifyProgram 
  = verify . parseString
  
verifyFile :: FilePath -> IO Bool
verifyFile fp
  = parseFile fp >>= verify
{-> parseFile "tests/par.input"

Prog {decls = [Bind {bvar = "s", bsort = Set},Bind {bvar = "m", bsort = Int},Bind {bvar = "g", bsort = Int},Bind {bvar = "id", bsort = Map (SetIdx "s") Int}]
, prog = Par "P" "s" TT (Seq [Seq [Assign (Bind {bvar = "id", bsort = Int}) (Const 0) "P",Assert (Atom Le (Const 0) (Var "id")) "P"] "",Seq [Assign (Bind {bvar = "id", bsort = Int}) (Bin Plus (Var "id") (Const 1)) "P",Assert (Atom Le (Const 0) (Var "id")) "P"] ""] "") "", ensures = Forall [Bind {bvar = "p", bsort = Int}] (Atom SetMem (Var "p") (Var "s") :=>: Atom Le (Const 0) (Select (Var "id") (Var "p")))}
-}

verify :: VCAnnot a
       => Program a
       -> IO Bool
verify p
  = do (inp, out, err, pid) <- runInteractiveProcess "z3" ["-smt2", "-in"] Nothing Nothing
       hPutStr inp vcstr
       -- putStrLn vcstr
       writeFile ".query.icet" (render (pp (coalesceLocal (prog p))))
       writeFile ".query.smt2" vcstr
       hFlush inp
       ec   <- waitForProcess pid
       outp <- hGetContents out
       errp <- hGetContents err
       case ec of
         ExitSuccess ->
           return ("unsat" `isInfixOf` outp)
           
         ExitFailure _ -> do
           putStrLn outp
           putStrLn errp
           return False
  where
    vcstr = render $ vcGen (decls p) (cardDecls p) (prog p) (ensures p)
-------------------------------------------------------------------------------
-- Build the VC
-------------------------------------------------------------------------------
vcGen :: VCAnnot a
      => [Binder]
      -> [Card a]
      -> Stmt a
      -> Prop a
      -> Doc
vcGen g ks s p
  = vcat (prelude : declBinds bs ++  [checkValid vc])
  where
    γ        = tyEnv g
    bs       = fmap (uncurry Bind) . M.toList $ tenv st
    (vc, st) = runState (replaceSorts (coalesceLocal s) >>= flip wlp  p)
                         (VCState { tenv = γ
                                  , constrs = M.empty
                                  , freshed = []
                                  , ictr = 0
                                  , invs = []
                                  , gather = False
                                  , cards = ks
                                  })

replaceSorts :: VCAnnot a => Stmt a -> VCGen a (Stmt a)
replaceSorts (Assign p x q e l)
  = do t <- getType (bvar x)
       return $ Assign p x { bsort = t } q e l
replaceSorts (Seq stmts l)
  = flip Seq l <$> mapM replaceSorts stmts
replaceSorts (ForEach x xs inv s l)
  = do g <- gets constrs
       ForEach x xs inv <$> replaceSorts s <*> pure l
       -- case M.lookup (process l) g of
       --   Nothing -> 
       --     ForEach x xs inv <$> replaceSorts s <*> pure l
       --   Just ps ->
       --     ForEach (liftSo x ps) xs inv <$> replaceSorts (subst (bvar x) xmap s) <*> pure l
  where
    liftSo x ps = x { bsort = Map (SetIdx ps) (bsort x) }
    xmap        = Select (Var (bvar x)) (Var (process l))
replaceSorts (If p s1 s2 l)
  = If p <$> replaceSorts s1 <*> replaceSorts s2 <*> pure l
replaceSorts (Par x xs inv s l)
  = do addElem xs x
       p <- Par x xs inv <$> replaceSorts s <*> pure l
       removeElem x
       return p
replaceSorts (Atomic s l)
  = flip Atomic l <$> replaceSorts s
replaceSorts s@(Assert _ _ _)
  = return s
replaceSorts s@(Assume _ _)
  = return s
replaceSorts s@(Skip _)
  = return s
replaceSorts s
  = error (printf "replaceSorts: %s" (show s))

coalesceLocal :: VCAnnot a => Stmt a -> Stmt a
coalesceLocal (Atomic s l)
  = Atomic s l
coalesceLocal (Par x xs sym s l)
  = Par x xs sym (coalesceLocal s) l
coalesceLocal (Seq [] l)
  = Skip l
coalesceLocal (Seq stmts@(s0:rest) l)
  | null pre
  = seqStmts l [coalesceLocal s0, coalesceLocal (Seq (coalesceLocal <$> rest) l)]
  | otherwise
  = seqStmts l [Atomic (seqStmts l pre) l, post']
  where
    (pre, post) = break (not . isLocal) stmts
    post'       = coalesceLocal (seqStmts l (coalesceLocal <$> post))
coalesceLocal (If p s1 s2 l)
  = If p (coalesceLocal s1) (coalesceLocal s2) l
coalesceLocal s = s

seqStmts :: a -> [Stmt a] -> Stmt a    
seqStmts l = flattenSeq . flip Seq l

flattenSeq :: Stmt  a -> Stmt a
flattenSeq (Seq ss l)
  = dropSingleton
  . simplifySkips
  $ Seq (foldl go [] ss') l
  where
    go ss (Seq ss' l) = ss ++ (foldl go [] ss')
    go ss (Skip _)    = ss
    go ss s           = ss ++ [s]
    ss'               = flattenSeq <$> ss
    dropSingleton (Seq [] l)  = Skip l
    dropSingleton (Seq [s] _) = s
    dropSingleton s           = s
flattenSeq (ForEach x y inv s l)
  = ForEach x y inv (flattenSeq s) l
flattenSeq s
  = s

simplifySkips :: Stmt a -> Stmt a
simplifySkips (Seq ss l) = Seq ss' l
  where ss'    = filter (not . isSkip) ss
        isSkip (Skip _) = True
        isSkip _        = False

isLocal (Assign p _ q _ _) = p == q
isLocal (Skip _)           = True
isLocal (Assert _ _ _)     = True
isLocal (Assume _ _)       = True
isLocal _                  = False
  

isIndex :: Sort -> Id -> VCGen a Bool
isIndex (Map (SetIdx ps) _) p
  = isElem p ps
isIndex _ _
  = return False

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM mb t e
  = do b <- mb
       if b then t else e

checkValid :: Prop a -> Doc
checkValid f = parens (text "assert" <+> smt (Not f)) $+$ text "(check-sat)"

declBinds :: [Binder] -> [Doc]
declBinds = map declBind
  where
    declBind (Bind x s) = parens (text "declare-const" <+> text x <+> smt s)

prelude :: Doc
prelude
  = text $ unlines [ "(define-sort Elt () Int)"
                   , "(define-sort Set () (Array Elt Bool))"
                   , "(define-sort IntMap () (Array Elt Elt))"
                   , "(define-fun set_emp () Set ((as const Set) false))"
                   , "(define-fun set_mem ((x Elt) (s Set)) Bool (select s x))"
                   , "(define-fun set_add ((s Set) (x Elt)) Set  (store s x true))"
                   , "(define-fun set_cap ((s1 Set) (s2 Set)) Set ((_ map and) s1 s2))"
                   , "(define-fun set_cup ((s1 Set) (s2 Set)) Set ((_ map or) s1 s2))"
                   , "(define-fun set_com ((s Set)) Set ((_ map not) s))"
                   , "(define-fun set_dif ((s1 Set) (s2 Set)) Set (set_cap s1 (set_com s2)))"
                   , "(define-fun set_sub ((s1 Set) (s2 Set)) Bool (= set_emp (set_dif s1 s2)))"
                   , "(define-fun set_minus ((s1 Set) (x Elt)) Set (set_dif s1 (set_add set_emp x)))"
                   , "(declare-fun set_size (Set) Int)"
                   ]

-------------------------------------------------------------------------------
-- Weakest Liberal Preconditions
-------------------------------------------------------------------------------
wlp :: VCAnnot a => Stmt a -> Prop a -> VCGen a (Prop a)   
wlp (Skip _) p
  = return p

-- Fresh var
wlp (Assign a x b NonDetValue c) p
  = do x' <- freshBinder x
       wlp (Assign a x b (Var (bvar x')) c) p

wlp (Assign a x b e l) p
  = do select <- isSet b
       v <-  case  e of
               Var y | b == a -> do t <- getType y
                                    ifM (isIndex t b)
                                        (return $ Select e (Var b))
                                        (return $ e)
               Var y | select
                       -> do t <- getType y
                             ifM (isIndex t b)
                                 (return $ Select e (Var b))
                                 (return e)
               _  -> return e
       g <- gets constrs
       
       ifM (isIndex (bsort x) pr)
             (return $ subst (bvar x) (Store (Var i) (Var pr) v) p)
             (return $ subst (bvar x) v p)
  where
    i  = bvar x
    pr = process l

wlp (Seq stmts _) p
  = foldM (flip wlp) p (reverse stmts)

wlp (Cases NonDetValue cs _) p
  = And <$> mapM (flip wlp p . caseStmt) cs

wlp (Cases e cs _) p
  = And <$> mapM go cs
  where
    go c
      = do wp <- wlp (caseStmt c) p
           return (Atom Eq e (caseGuard c)  :=>: wp)

wlp (ForEach x xs (rest, i) s _) p
  = do addElem (bvar xs) (bvar x)
       i'  <- gathering $ wlp s TT
       let i'' = subst (bvar xs) erest i'
       let inv = and [i, Forall [x] (and [ Atom SetMem ex erest ] :=>: i'')]
       pre <- wlp s $ subst rest (Bin SetAdd erest ex) inv
       removeElem (bvar x)
       return $ And [ subst rest EmptySet inv
                    , Forall vs $ and [ inv
                                      , Atom SetMem ex exs 
                                      , Not $ Atom SetMem ex erest
                                      ]
                                  :=>:
                                  pre
                    , Forall vs $ subst rest (Var (bvar xs)) inv :=>: p
                    ]
  where
    ex        = Var (bvar x)
    exs       = Var (bvar xs)
    erest     = Var rest
    vs        = x : Bind rest Set : writes s

wlp (Par i is _ s _) p
  = do modify $ \s -> s { tenv = M.insert (pcName is) (Map (SetIdx is) Int) (tenv s) }
       addElem is i
       bs      <- vcBinds
       let (pc0, acts, outs) = as bs
           actsLocs     = replaceHere i is <$> acts
           exitCond     = Or [pcGuard i is x | x <- outs]

       inv     <- actionsInvariant i is actsLocs

       let qInv = and [ inv
                      , (Forall [Bind i0 Int] (pcGuard i0 is (-1)))
                      ] :=>: p
           init = Forall [Bind i0 Int] $ and [ Atom SetMem (Var i0) (Var is)
                                             , or [ pcGuard i0 is pc0i | pc0i <- pc0 ]
                                             ]
           initial = init :=>: Forall [Bind i0 Int] (subst i (Var i0) inv)
       txns    <- mapM (wlpAction i is inv) actsLocs
       removeElem i
       return $ and ([initial] ++ txns ++ [Forall bs qInv]) 
  where
    as bs = actions i s bs
    i0    = i ++ "!"

wlp (Assert b pre _) p
  = do g <- gets gather
       if (g && pre) || (not g && not pre) then
         return (and [b, p])
       else
         return p

wlp (Assume b _) p
  = do g <- gets gather
       return (if g then p else b :=>: p)

wlp (If c s1 s2 _) p
  = do φ <- wlp s1 p
       ψ <- wlp s2 p
       let guard p q = case c of
                         NonDetProp -> [p, q]
                         _          -> [c :=>: p, Not c :=>: q]
       return . and $ guard φ ψ

wlp (Atomic s _) p
  = wlp s p

wlp s _
  = error (printf "wlp TBD: %s" (show s))
-------------------------------------------------------------------------------
-- Build Invariant from Assertions
-------------------------------------------------------------------------------
actionsInvariant :: (Show a, Process a)
                 => Id
                 -> Id
                 -> [Action a]
                 -> VCGen a (Prop a)
actionsInvariant p ps as
  = do e <- gets tenv
       cs <- gets constrs
       p <- and <$> mapM (oneConj e cs) as
       modify $ \st -> st { tenv = e }
       return p
  where
    oneConj e cs (Action xs us _ _ _ s)
     = gathering $ do
         modify $ \st -> st { tenv = M.union (tyEnv xs) e }
         forM us $ \(p,ps) -> addElem ps p
         wlp s TT

-------------------------------------------------------------------------------
-- Actions
-------------------------------------------------------------------------------
wlpAction :: (Process a, Show a)
          => Id
          -> Id
          -> Prop a
          -> Action a
          -> VCGen a (Prop a)
wlpAction p ps inv (Action xs us pcond i outs s)
  = do ks        <- gets cards
       c0        <- gets constrs
       xs0       <- gets tenv
       let tenv' = M.union (tyEnv (Bind p Int : xs)) xs0
       modify $ \st -> seq g st { constrs = M.union (M.fromList us) c0, tenv = tenv'  }
       inductive <- wlp s post
       modify $ \st -> st { constrs = c0, tenv = xs0 }
       return $ Forall xs (Let (cardsInits ks ((p,ps):us)) {- }(initialCards p ks (updateCandidates p us)) -}
                           (g :=>: inductive))
  where
    post    = and [ invAt o | o <- outLocs ]
    invAt l = subst (pcName ps) (Store (Var (pcName ps)) (Var p) (Const l)) inv
    outLocs = if null outs then [-1] else snd <$> outs
    g       = and [ pathGuard pcond, Atom SetMem (Var p) (Var ps), pcGuard p ps i, inv ]

cardsInits ks us
  = [ bind k p q | k <- ks, (p,ps) <- us, cardOwner k == ps, (q,qs) <- us, ps /= qs ]
  where
    bind k p q = (Bind (initialBool k p q) Bool, PExpr (evalCardFormula k p q))

initialCards p ks qs  
  = [ bind k p q | k <- ks, q <- qs ]
  where
    bind k p q = (Bind (initialBool k p q) Bool, PExpr (evalCardFormula k p q))

updateCandidates :: Id -> [(Id, Id)] -> [Id]
updateCandidates p us
  = [ q | (q,qs) <- us, q /= p ]

updateCard :: Card a -> Id -> [Id] -> Expr a
updateCard k p qs
  = Store kexp (Var p) updVal
  where
    updVal   = foldl' go (Select kexp (Var p)) qs
    go a q   = Bin Plus a $ Bin Minus (Ite (incrCond q) (Const 1) (Const 0))
                                      (Ite (decrCond q) (Const 1) (Const 0))
    kexp     = Var (cardName k)
    incrCond q = and [Not (PVar (initialBool k p q)), evalCardFormula k p q]
    decrCond q = and [PVar (initialBool k p q), Not (evalCardFormula k p q)]

initialBool :: Card a -> Id -> Id -> Id
initialBool k p q
  = cardName k ++ "!" ++ p ++ "!" ++ q

-- initialVal k p
--   = do cs <- M.toList <$> gets constrs
--        let cs'   = [ evalCardFormula k p q | (qs,q) <- cs,  q /= p ]
--        undefined
--   where
--     go (Const 0) q = evalCardFormula k p q
--     go a         q = Bin Plus a (evalCardFormula k p q)

evalCardFormula k p q
  = subst (cardElem k) (Var q)
          (subst (cardId k) (Var p) (cardProp k))
  

pathGuard :: [Prop a] -> Prop a
pathGuard []   = TT
pathGuard [p]  = p
pathGuard ps   = and ps

pcGuard :: Id -> Id -> Int -> Prop a
pcGuard p ps i = Atom Eq (pc ps p) (Const i)


replaceHere :: t -> Id -> Action a -> Action a
replaceHere _ ps (Action xs us cond i outs s)
 = Action xs us cond i outs (goStmt s)
  where
    goStmt (Assert φ b l)
      = Assert (goProp φ) b l
    goStmt (Seq stmts l)
      = Seq (goStmt <$> stmts) l
    goStmt (If c s1 s2 l)
      = If c (goStmt s1) (goStmt s2) l
    goStmt (ForEach x xs inv s l)
      = ForEach x xs inv (goStmt s) l
    goStmt s
      = s

    goProp (Here e)
      = Atom Eq (Select (Var (pcName ps)) e) (Const i)
    goProp (Forall xs a)
      = Forall xs $ goProp a
    goProp (a :=>: b)
      = goProp a :=>: goProp b
    goProp (And as)
      = And (goProp <$> as)
    goProp (Or as)
      = Or (goProp <$> as)
    goProp (Not a)
      = Not $ goProp a
    goProp a
      = a
--   = Seq (replaceHere i <$> stmts) l
-- replaceHere i is (Assert p l)
--   = Assert (hereProp i p) l

-- hereProp i (Here e)
--   = pcName

  
-------------------------------------------------------------------------------
-- Monads
-------------------------------------------------------------------------------
data VCState a = VCState { tenv  :: M.Map Id Sort
                         , constrs :: M.Map Id Id
                         , ictr :: Int
                         , freshed :: [Binder]
                         , invs :: [(Int, [Binder], Prop a)]
                         , cards :: [Card a]
                         , gather :: Bool
                         }
type VCGen a r = State (VCState a) r 

cardsFor :: Id -> VCGen a [Card a]
cardsFor ps
  = do cs <- gets cards
       return $ [ c | c <- cs, cardOwner c == ps ]

freshBinder :: Binder -> VCGen a Binder
freshBinder (Bind x _)
  = do i <- gets ictr
       t <- getType x
       let var = (x ++ "!" ++ show i)
       let b' = Bind var t
       modify $ \s -> s { ictr = i + 1, freshed = b' : freshed s, tenv = M.insert var  t (tenv s)}
       return b'

gathering :: VCGen a b -> VCGen a b  
gathering mact
  = do modify $ \s -> s { gather = True }
       r <- mact
       modify $ \s -> s { gather = False }
       return r

tyEnv :: [Binder] -> M.Map Id Sort
tyEnv bs = M.fromList [ (x,t) | Bind x t <- bs ]

vcBinds :: VCGen a [Binder]
vcBinds =  fmap (uncurry Bind) . M.toList <$> gets tenv

addElem :: Id -> Id -> VCGen a ()  
addElem ps p
  = modify $ \s -> s { constrs = M.insert p ps (constrs s) }

removeElem :: Id -> VCGen a ()
removeElem p
  = modify $ \s -> s { constrs = M.delete p (constrs s) }

isElem :: Id -> Id -> VCGen a Bool
isElem p ps
  = do g <- gets constrs
       return $ maybe False (==ps) $ M.lookup p g

isSet :: Id -> VCGen a Bool
isSet i
  = do g <- gets constrs
       return $ M.member i g

getType :: Id -> VCGen a Sort
getType x
  = do γ <- gets tenv
       case M.lookup x γ of
         Just t  -> return t
         Nothing -> error (printf "Unknown id: %s" x)
-------------------------------------------------------------------------------
-- Scratch
-------------------------------------------------------------------------------
-- testLoop :: Stmt a
-- testLoop =
--   ForEach (Bind "x" Int) (Bind "xs" Set)
--     ("rest", Forall [Bind "i" Int] $
--                Atom SetMem (Var "i") (Var "rest") :=>:
--                Atom Eq (Var "i") (Const 1))
--     (Bind "y" Int :<-: Const 0)

-- testProp :: Prop a
-- testProp =
--   Forall [Bind "i" Int] $
--     (Atom SetMem (Var "i") (Var "xs")) :=>:
--     (Atom Eq (Var "i") (Const 0))

-------------------
-- Two Phase Commit
-------------------
-- vint :: Id -> Binder
-- vint x = Bind x Int

-- vmap :: Id -> Binder
-- vmap x = Bind x (Map IntIdx Int)

-- vset :: Id -> Binder
-- vset x = Bind x Set

-- twoPhaseDecls :: [Binder]
-- twoPhaseDecls = [ vint "proposal"
--                 , vset "P"
--                 , vint "committed"
--                 , vint "abort"
--                 , vmap "val"
--                 , vmap "value"
--                 , vint "c"
--                 , vmap "id"
--                 , vint "msg"
--                 , vmap "pmsg"
--                 , vint "reply"
--                 ]

-- twoPhase :: Stmt ()
-- twoPhase
--   = Seq [ vint "committed" :<-: false
--         , vint "abort" :<-: false

--         , ForEach (vint "p") (Bind "P" Set)
--           ( "_rest"
--           , Forall [Bind "i" Int]
--             ( Atom SetMem (Var "i") (Var "_rest")
--               :=>:
--               Atom Eq (Select (Var "val") (Var "i"))
--               (Var "proposal")
--             )
--           ) $
--           Seq [ vmap "id"  :<-: Store (Var "id") (Var "p") (Var "c")
--               , vmap "val" :<-: Store (Var "val") (Var "p") (Var "proposal")
--               ] ()

--         , ForEach (vint "p") (Bind "P" Set)
--           ( "_rest"
--           , Forall [Bind "i" Int] $
--             And [ Atom SetMem (Var "i") (Var "_rest")
--                 , Atom Eq (Var "committed") true
--                 ]
--             :=>:
--             Atom Eq (Select (Var "value") (Var "i"))
--                     (Select (Var "val") (Var "i"))
--           )
--           (Seq [ vint "ndet" :<-: NonDetValue
--                , Cases (Var "ndet") [ Case true $
--                                       Seq [ vint "msg"  :<-: vcommit
--                                           , vmap "pmsg" :<-: Store (Var "pmsg") (Var "p") vcommit
--                                           ]
--                                       ()
                               
--                                     , Case false $
--                                       Seq [ vint "msg"   :<-: vabort
--                                           , vint "abort" :<-: true
--                                           , vmap "pmsg"  :<-: Store (Var "pmsg") (Var "p") vabort
--                                           ]
--                                       ()
--                                     ]
--                  ()
--                ]
--             ())

--         , Cases (Var "abort") [ Case false $
--                                 Seq [ vint "reply" :<-: vcommit
--                                     , vint "committed" :<-: true
--                                     ]
--                                 ()

--                               , Case true $
--                                 vint "reply" :<-: vabort
--                               ]
--         ()
--         , ForEach (vint "p") (Bind "P" Set)
--           ("_rest", TT) $
--           Seq [ vmap "decision" :<-: Store (Var "decision") (Var "p") (Var "reply")
--               , Cases (Select (Var "decision") (Var "p"))
--                 [ Case vcommit $
--                   vmap "value" :<-: Store (Var "value") (Var "p") (Select (Var "val") (Var "p"))

--                 , Case vabort $
--                   Skip ()
--                 ]
--                 ()
--               ]
--           ()
--         ]
--     ()
--   where
--     false = Const 0
--     true  = Const 1

--     vabort  = Const 0
--     vcommit = Const 1

-- twoPhaseDebug :: Prop ()
-- twoPhaseDebug
--   = Forall [vint "i"] $
--       And [ Atom SetMem (Var "i") (Var "P") ]
--       :=>:
--       Atom Eq (Select (Var "val") (Var "i")) (Var "proposal")

-- twoPhaseSafety :: Prop ()
-- twoPhaseSafety
--   = Forall [vint "i"] $
--       And [ Atom SetMem (Var "i") (Var "P"), Atom Eq (Var "committed") (Const 1) ]
--       :=>: FF
      -- Atom Eq (Var "proposal")
      --         (Select (Var "value") (Var "i"))
{-> vcGen twoPhaseDecls twoPhase twoPhaseSafety
-}
