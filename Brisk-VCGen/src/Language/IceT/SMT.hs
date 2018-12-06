module Language.IceT.SMT where
import Language.IceT.Types
import Text.PrettyPrint.HughesPJ

class SMT a where
  smt :: a -> Doc

instance SMT (Prop a) where
  smt TT             = text "true"
  smt FF             = text "false"
  smt (Atom r e1 e2) = parens (smt r <+> smt e1 <+> smt e2)
  smt (Not p)        = parens (text "not" <+> (smt p))
  smt (And ps)       = parens (text "and" <+> vcat (fmap smt ps))
  smt (Or ps)        = parens (text "or"  $$ vcat (fmap smt ps))
  smt (p :=>: q)     = parens (text "=>" <+> (smt p $+$ smt q))
  smt (Forall xs p)  = parens (text "forall" <+> vcat [parens (vcat (fmap smt xs)), smt p])
  smt (Exists xs p)  = parens (text "exists" <+> vcat [parens (vcat (fmap smt xs)), smt p])
  smt (Let xs p)     = parens (text "let" <+> b $+$ smt p)
    where
      b = parens (vcat [parens (text (bvar x) <+> smt e) | (x,e) <- xs])
  smt (Prop e)       = smt e
  smt NonDetProp     = error "NonDetProp"
  smt (Here _)       = error "Here"
  smt (PVar _)       = error "PVar"
instance SMT Binder where
  smt b = parens (text (bvar b) <+> smt (bsort b))

instance SMT Index where
  smt _ = smt Int

instance SMT Sort where
  smt Bool      = text "Bool"
  smt Int       = text "Int"
  smt Set       = text "Set"
  smt (Map s t) = parens (text "Array" <+> smt s <+> smt t)

instance SMT (Expr a) where
  smt NonDetValue   = error "nondetvalue"
  smt (Const i)     = int i
  smt (Var x)       = text x
  smt (Bin o e1 e2) = parens (smt o <+> smt e1 <+> smt e2)
  smt (Select x y)  = parens (text "select" <+> smt x <+> smt y)
  smt (Store x y z) = parens (text "store" <+> smt x <+> smt y <+> smt z)
  smt (Size e)      = parens (text "set_size" <+> smt e)
  smt EmptySet      = text "set_emp"
  smt (Ite p x y)   = parens (text "ite" <+> smt p $+$ smt x $+$ smt y)
  smt (PExpr e)     = smt e

instance SMT Op where
  smt Plus  = text "+"
  smt Minus = text "-"
  smt SetSubSingle = text "set_minus"
  smt SetAdd = text "set_add"
  smt Mul    = text "*"
  smt Div    = text "/"
  
instance SMT Rel where
  smt Eq     = text "="
  smt Lt     = text "<"
  smt Gt     = text ">"
  smt Le     = text "<="
  smt SetMem = text "set_mem"
