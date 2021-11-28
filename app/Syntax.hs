module Syntax where
import qualified Data.Set as Set

type Var = String

data Lit = LUnit | LInt Int | LBool Bool {-| LArray [Lit]-} deriving (Show)

data BinOp = BPlus | BMinus | BTimes | BDiv | BMod | BAnd | BOr | BGeq | BLeq | BNeq | BEq | BGt | BLt {-| BIndex-} deriving (Show)

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

data Typ = TyUnit | TyInt | TyBool {-| TyArr Typ-}
data Method = Method {name :: String, args :: [(Var,Typ)], retTy :: Typ, retName :: Var, body :: Cmd, pres :: [Prop], posts :: [Prop]}


{- Language of propositions -}
data NumExpBinOp = NEPlus | NEMinus | NETimes {-| NEDiv | NEMod-} deriving (Eq,Ord)
instance Show NumExpBinOp where
  show NEPlus = "+"
  show NEMinus = "-"
  show NETimes = "*"

data NumExpMonOp = NENeg deriving (Eq,Ord)
instance Show NumExpMonOp where
  show NENeg = "-"

{- Multilinear expressions ONLY -}
data NumExp = NEVar Var | NEInt Int | NEBinOp NumExpBinOp NumExp NumExp | NEMonOp NumExpMonOp NumExp deriving (Eq,Ord)
instance Show NumExp where
  show (NEVar x) = x
  show (NEInt n) = show n
  show (NEBinOp b e1 e2) = "(" ++ show e1 ++ " " ++ show b ++ " " ++ show e2 ++ ")"
  show (NEMonOp m e) = show m ++ show e

data PropRel = RGeq | RLeq | REq | RGt | RLt | RNeq
instance Show PropRel where
  show RGeq = ">="
  show RLeq = "<="
  show REq = "=="
  show RGt = ">"
  show RLt = "<"
  show RNeq = "!="

data PropBinOp = PAnd | POr
instance Show PropBinOp where
  show PAnd = "&&"
  show POr = "||"

data PropMonOp = PNot
instance Show PropMonOp where
  show PNot = "!"

data Prop = {-PropVar Var | -}PropConst Bool | RelExp PropRel NumExp NumExp | PBO PropBinOp Prop Prop | PMO PropMonOp Prop
instance Show Prop where
  show (PropConst b) = show b
  show (RelExp r e1 e2) = show e1 ++ " " ++ show r ++ " " ++ show e2
  show (PBO r p1 p2) = "(" ++ show p1 ++ " " ++ show r ++ " " ++ show p2 ++ ")"
  show (PMO m p) = show m ++ "(" ++ show p ++ ")"

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
{-notProp (PropVar x) = PMO PNot (PropVar x)-}
notProp (RelExp r x y) = RelExp (notRel r) x y
notProp (PBO PAnd x y) = PBO POr (notProp x) (notProp y)
notProp (PBO POr x y) = PBO PAnd (notProp x) (notProp y)
notProp (PMO PNot x) = driveNegations x
notProp (PropConst b) = PropConst (not b)

driveNegations :: Prop -> Prop
{-driveNegations (PropVar x) = PropVar x-}
driveNegations (RelExp r e1 e2) = RelExp r e1 e2
driveNegations (PBO r p1 p2) = PBO r (driveNegations p1) (driveNegations p2)
driveNegations (PMO PNot p) = notProp p
driveNegations (PropConst b) = PropConst b