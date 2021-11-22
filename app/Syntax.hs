module Syntax where

type Var = String

data Lit = LUnit | LInt Int | LBool Bool | LArray [Lit] deriving (Show)

data BinOp = BPlus | BMinus | BTimes | BDiv | BMod | BAnd | BOr | BGeq | BLeq | BNeq | BEq | BGt | BLt | BIndex deriving (Show)

data MonOp = MNeg | MNot | MLength deriving (Show)

data Expr = EVar Var | ELit Lit | EBinOp BinOp Expr Expr | EMonOp MonOp Expr deriving (Show)

data LVal = LVar Var | LIndex Var Expr deriving (Show)


data Cmd
  = Assign LVal Expr
  | Seq [Cmd]
  | IfElse Expr Cmd Cmd
  | While Expr Cmd
  | Skip
  | Return Expr
  deriving (Show)

data Typ = TyUnit | TyInt | TyBool | TyArr Typ
data Method = Method {name :: String, args :: [(Var,Typ)], retTy :: Typ, retName :: Var, body :: Cmd, pres :: [Prop], posts :: [Prop]}


{- Language of propositions -}
data NumExpBinOp = NEPlus | NEMinus | NETimes | NEDiv | NEMod
data NumExpMonOp = NENeg
data NumExp = NEVar Var | NEInt Int | NEBinOp NumExpBinOp NumExp NumExp | NEMonOp NumExpMonOp NumExp
data PropRel = RGeq | RLeq | REq | RGt | RLt | RNeq
data PropBinOp = PAnd | POr
data PropMonOp = PNot
data Prop = PropVar Var | RelExp PropRel NumExp NumExp | PBO PropBinOp Prop Prop | PMO PropMonOp Prop
