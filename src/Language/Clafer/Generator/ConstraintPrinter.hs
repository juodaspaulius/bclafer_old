
module Language.Clafer.Generator.ConstraintPrinter where
import Prelude hiding (exp)
import Data.Char
import Data.List
import Data.Maybe
import Data.Function

import Debug.Trace

import Language.Clafer.Common
import Language.Clafer.Intermediate.Intclafer 



class Show a => ConstrShow a where
  cshow :: a -> String
  cshow x = show x

instance ConstrShow IModule where
  cshow imodule = intercalate "\n" $  map cshow decls 
    where 
    decls = mDecls imodule

instance ConstrShow IElement where
  cshow (IEClafer clafer) = "clafer " ++ (ident clafer) ++
    ":\n"  ++ (intercalate " && " $ map cshow constraints) ++
    (intercalate "\n" $ map cshow subclafers)
    where
    constraints =  [ x | x@(IEConstraint {}) <- (elements clafer)] 
    subclafers =  [ x | x@(IEClafer {}) <- (elements clafer)] 
  cshow (IEConstraint _ exp) = cshow exp
  cshow (IEGoal _ _) = "" 

instance ConstrShow PExp where
  cshow (PExp _ _ _ e) = cshow e

instance ConstrShow IExp where
  cshow x@(IFunExp op [e1]) 
    | op == iNot = "!" ++ e1'
    | op == iCSet = "#" ++ e1'
    | op == iMin = "- " ++ e1'
    | op == iGMax = "max " ++ e1'
    | op == iGMin = "min " ++ e1'
    | op == iSumSet = "sum " ++ e1'
    | op == iF = "<> " ++ e1'
    | op == iG=  "[] " ++ e1'
    | op == iX = "X " ++ e1'
    where
    e1' = cshow e1
  cshow x@(IFunExp op [e1, e2])
    | op == iIff = "(" ++ e1' ++ " <-> " ++ e2'  ++ ")"
    | op == iImpl = "(" ++ e1' ++ " -> " ++ e2'  ++ ")"
    | op == iOr = "(" ++ e1' ++ " || " ++ e2'  ++ ")"
    | op == iXor ="(" ++ e1' ++ " xor " ++ e2'  ++ ")"
    | op == iAnd ="(" ++ e1' ++ " && " ++ e2'  ++ ")"
    | op == iU ="(" ++ e1' ++ " U " ++ e2'  ++ ")"
    | op == iR ="(" ++ e1' ++ " R " ++ e2'  ++ ")"
    | op == iW ="(" ++ e1' ++ " W " ++ e2'  ++ ")"
    | op == iLt ="(" ++ e1' ++ " < " ++ e2'  ++ ")"
    | op == iGt ="(" ++ e1' ++ " > " ++ e2'  ++ ")"
    | op == iEq =(cshow e1 ) ++ "_eq_" ++ (cshow e2)
    | op == iLte ="(" ++ e1' ++ " <= " ++ e2'  ++ ")"
    | op == iGte ="(" ++ e1' ++ " >= " ++ e2'  ++ ")"
    | op == iNeq ="(" ++ e1' ++ " != " ++ e2'  ++ ")"
    | op == iIn ="(" ++ e1' ++ " in " ++ e2'  ++ ")"
    | op == iNin ="(" ++ e1' ++ " not in " ++ e2'  ++ ")"
    | op == iJoin =  (cshow e1) ++ (cshow e2)
    where 
    e1' = "(" ++ (cshow e1) ++ ")"
    e2' = "(" ++ (cshow e2) ++ ")"
  cshow (IClaferId _ id _ _ _) = id
  cshow (IDeclPExp q decl e) = (map toLower $ show q) ++ "_" ++ (cshow e)
  cshow x = show x
    


printModuleConstraints :: IModule -> String
printModuleConstraints imodule = cshow imodule
{-unlines map cshow decls-}
    {-where decls = mDecls imodule-}
 
    
