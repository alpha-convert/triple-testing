module Syntax where
import qualified Data.Set as Set

type Var = String

data Lit = LUnit | LInt Int | LBool Bool {-| LArray [Lit]-} deriving (Show)

data BinOp = BPlus | BMinus | BTimes | BDiv | BMod | BAnd | BOr | BGeq | BLeq | BNeq | BEq | BGt | BLt | BIndex deriving (Show)

data MonOp = MNeg | MNot | MLength deriving (Show)

data Expr = EVar Var | ELit Lit | EBinOp BinOp Expr Expr | EMonOp MonOp Expr deriving (Show)

data LVal = LVar Var {-| LIndex Var Expr -} deriving (Show)


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
data NumExpBinOp = NEPlus | NEMinus | NETimes {-| NEDiv | NEMod-} deriving (Show)
data NumExpMonOp = NENeg deriving (Show)
data NumExp = NEVar Var | NEInt Int | NEBinOp NumExpBinOp NumExp NumExp | NEMonOp NumExpMonOp NumExp deriving (Show)
data PropRel = RGeq | RLeq | REq | RGt | RLt | RNeq deriving (Show)
data PropBinOp = PAnd | POr deriving (Show)
data PropMonOp = PNot deriving (Show)
data Prop = PropVar Var | RelExp PropRel NumExp NumExp | PBO PropBinOp Prop Prop | PMO PropMonOp Prop deriving (Show)

freeNumVar :: NumExp -> Set.Set Var
freeNumVar (NEVar x) = Set.singleton  x
freeNumVar (NEInt _) = Set.empty
freeNumVar (NEBinOp _ e1 e2) = Set.union (freeNumVar e1) (freeNumVar e2)
freeNumVar (NEMonOp _ e) = freeNumVar e

notRel :: PropRel -> PropRel
notRel RGeq = RLt
notRel RLeq = RGt
notRel REq = RNeq
notRel RGt = RLeq
notRel RLt = RGeq
notRel RNeq = REq

notProp :: Prop -> Prop
notProp (PropVar x) = PMO PNot (PropVar x)
notProp (RelExp r x y) = RelExp (notRel r) x y
notProp (PBO PAnd x y) = PBO POr (notProp x) (notProp y)
notProp (PBO POr x y) = PBO PAnd (notProp x) (notProp y)
notProp (PMO PNot x) = driveNegations x

driveNegations :: Prop -> Prop
driveNegations (PropVar x) = PropVar x
driveNegations (RelExp r e1 e2) = RelExp r e1 e2
driveNegations (PBO r p1 p2) = PBO r (driveNegations p1) (driveNegations p2)
driveNegations (PMO PNot p) = notProp p