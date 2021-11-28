module Semantics where

import Syntax
import Data.Map as Map
import Data.Sequence as Seq hiding (zip)
import Control.Monad.Except
import Control.Monad.State.Lazy
import Control.Monad.Identity

data Val = VUnit | VInt Int | VBool Bool {-| VArray (Seq.Seq Val)-} deriving (Show,Eq)

litToVal :: Lit -> Val
litToVal LUnit = VUnit
litToVal (LInt x) = VInt x
litToVal (LBool x) = VBool x
-- litToVal (LArray x) = VArray (Seq.fromList $ fmap litToVal x)

type Store = Map.Map Var Val

data Err = Fail String | TypeErr String deriving (Show,Eq)

type Comp a = StateT Store (Except Err) a

runComp :: Comp a -> Store -> Either Err (a,Store)
runComp m s = runIdentity $ runExceptT $ runStateT m s

lookupVar :: Var -> Comp Val
lookupVar x = do
  m <- get
  case Map.lookup x m of
    Just v -> return v
    _ -> throwError (Fail ("Could not find variable " ++ x))

{-data BinOp = BPlus | BMinus | BTimes | BDiv | BMod | BAnd | BOr | BGeq | BEq | BGt | BLt | BIndex deriving (Show)-}
evalBinOp :: BinOp -> Val -> Val -> Val
evalBinOp BPlus (VInt x) (VInt y) = VInt (x + y)
evalBinOp BMinus (VInt x) (VInt y) = VInt (x - y)
evalBinOp BTimes (VInt x) (VInt y) = VInt (x * y)
evalBinOp BDiv (VInt x) (VInt y) = VInt (x `div` y)
evalBinOp BMod (VInt x) (VInt y) = VInt (x `mod` y)
evalBinOp BAnd (VBool x) (VBool y) = VBool (x && y)
evalBinOp BOr (VBool x) (VBool y) = VBool (x || y)
evalBinOp BGeq (VInt x) (VInt y) = VBool (x >= y)
evalBinOp BLeq (VInt x) (VInt y) = VBool (x <= y)
evalBinOp BEq (VInt x) (VInt y) = VBool (x == y)
evalBinOp BNeq (VInt x) (VInt y) = VBool (x /= y)
evalBinOp BGt (VInt x) (VInt y) = VBool (x > y)
evalBinOp BLt (VInt x) (VInt y) = VBool (x < y)
-- evalBinOp BIndex (VArray xs) (VInt x) = xs `Seq.index` x
evalBinOp _ _ _ = undefined

{-data MonOp = MNeg | MNot deriving (Show)-}
evalMonOp :: MonOp -> Val -> Val
evalMonOp MNeg (VInt x) = VInt (- x)
evalMonOp MNot (VBool b) = VBool (not b)
-- evalMonOp MLength (VArray xs) = VInt (Seq.length xs)
evalMonOp _ _ = undefined

{-data Expr = EVar Var | ELit Lit | EBinOp BinOp Expr Expr | EMonOp MonOp Expr deriving (Show)-}
evalExpr :: Expr -> Comp Val
evalExpr (EVar x) = lookupVar x
evalExpr (ELit l) = return $ litToVal l
evalExpr (EBinOp bo e1 e2) = evalBinOp bo <$> evalExpr e1 <*> evalExpr e2
evalExpr (EMonOp mo e) = evalMonOp mo <$> evalExpr e

assignVar :: Var -> Val -> Comp ()
assignVar x v = do
  sto <- get
  put $ Map.insert x v sto

{-
setIndex :: Var -> Int -> Val -> Comp ()
setIndex x i v = do
  sto <- get
  let ma = Map.lookup x sto
  case ma of
    Just (VArray xs) ->
      if i >= Seq.length xs then throwError (Fail "Out of range update")
      else do
      let xs' = Seq.adjust (const v) i xs
      let sto' = Map.insert x (VArray xs') sto
      put sto'
    Just _ -> throwError (TypeErr "Got non-array value to index into")
    Nothing -> throwError (Fail ("Unbound variable " ++ x))
-}

runCmd :: Cmd -> Comp Val
runCmd (Assign (LVar x) e) = evalExpr e >>= assignVar x >> return VUnit
{-runCmd (Assign (LIndex x idx) e) = do
  v <- evalExpr e
  vi <- evalExpr idx
  case vi of
    VInt i -> setIndex x i v >> return VUnit
    _ -> throwError (TypeErr "Got non-integer index.")
-}
runCmd (Seq cs) = foldM (const runCmd) VUnit cs
runCmd (IfElse e c1 c2) = do
  v <- evalExpr e
  case v of
    VBool True -> runCmd c1
    VBool False -> runCmd c2
    v -> throwError (TypeErr $ "Non-bool branch condition " ++ show v)
runCmd (While e c) = do
  v <- evalExpr e
  case v of
    VBool False -> return VUnit
    VBool True -> runCmd c >> runCmd (While e c)
    v -> throwError (TypeErr $ "Non-bool loop condition " ++ show v)
runCmd Skip = return VUnit
runCmd (Return e) = evalExpr e

call :: Method -> [Val] -> Comp Val
call m vs = do
  let argnames = fst <$> args m
  let sto = Map.fromList $ zip argnames vs
  let c = body m
  withStateT (Map.unionWith const sto) (runCmd c)


{- Propositional semantics -}
{-data NumExp = NumLitInt Int | NumExpPlus NumExp NumExp | NumExpMinus NumExp NumExp | NumExpTimes NumExp NumExp | NumExpDiv NumExp NumExp | NumExpMod NumExp NumExp-}
evalNumExp :: Integral a => NumExp -> Comp a
evalNumExp (NEVar x) = do
  v <- lookupVar x
  case v of
    VInt v -> return $ fromInteger $ toInteger v
    _ -> throwError (TypeErr "Got non-numeric type while evaluating NumExp")
evalNumExp (NEInt x) = return $ fromInteger $ toInteger x
evalNumExp (NEBinOp b e1 e2) = evalNEBinOp b <$> evalNumExp e1 <*> evalNumExp e2
evalNumExp (NEMonOp o e) = evalNEMonOp o <$> evalNumExp e

evalProp :: Prop -> Comp Bool
{-evalProp (PropVar x) = do
  v <- lookupVar x
  case v of
    VBool b -> return b
    _ -> throwError (TypeErr "Got non-propositional variable")
-}
evalProp (RelExp r p1 p2) = evalPropRel r <$> evalNumExp p1 <*> evalNumExp p2
evalProp (PBO op p1 p2) = evalPropBinOp op <$> evalProp p1 <*> evalProp p2
evalProp (PMO op p) = evalPropMonOp op <$> evalProp p
evalProp (PropConst b) = return b

evalPropMonOp :: PropMonOp -> Bool -> Bool
evalPropMonOp PNot = not

evalPropBinOp :: PropBinOp -> Bool -> Bool -> Bool
evalPropBinOp PAnd = (&&)
evalPropBinOp POr = (||)

evalPropRel :: (Ord a, Eq a) => PropRel -> a -> a -> Bool
evalPropRel RLeq = (<=)
evalPropRel RGeq = (>=)
evalPropRel RLt = (<)
evalPropRel RGt = (>)
evalPropRel REq = (==)
evalPropRel RNeq = (/=)


evalNEMonOp :: Num a => NumExpMonOp -> a -> a
evalNEMonOp NENeg = ((-1)*)

evalNEBinOp :: Num a => NumExpBinOp -> a -> a -> a
evalNEBinOp NEPlus = (+)
evalNEBinOp NEMinus = (-)
evalNEBinOp NETimes = (*)
{-evalNEBinOp NEDiv = div
evalNEBinOp NEMod = mod-}
