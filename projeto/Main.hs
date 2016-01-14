import qualified Language.ECMAScript3.Parser as Parser
import Language.ECMAScript3.Syntax
import Control.Monad hiding (empty)
import Control.Applicative hiding (empty)
import Data.Map as Map
import Debug.Trace
import Value

--
-- Evaluate functions
--

evalExpr :: StateT -> Expression -> StateTransformer Value
evalExpr env (VarRef (Id id)) = stateLookup env id
evalExpr env (IntLit int) = return $ Int int
evalExpr env (InfixExpr op expr1 expr2) = do
    v1 <- evalExpr env expr1
    v2 <- evalExpr env expr2
    infixOp env op v1 v2
evalExpr env (AssignExpr OpAssign (LVar var) expr) = do
    v <- stateLookup env var
    case v of
        -- Variable not defined :(
        (Error _) -> do
            e <- evalExpr env expr
            setVar var e
        -- Variable defined, let's set its value
        _ -> do
            e <- evalExpr env expr
            setVar var e
---------------------------- i++ and i-- -----------------------------------------------
evalExpr env (UnaryAssignExpr unOp (LVar var)) = do
    ret <- stateLookup env var
    case ret of
        (Error _) -> return $ Error $ (show var) ++ " not defined"
        _ -> do
            b <-  postfixOp env unOp (ret)
            setVar var b
--------------------------- dotRef -----------------------------------------
evalExpr env (DotRef expr (Id a)) = do 
    ret <- evalExpr env expr 
    case ret of
        (List []) -> return Nil
        (List (x:xs)) -> if (a == "head") then return (ListRet x) else if (a == "tail") then return (List xs) else return Nil 

------------------------------------- List ---------------------------------------------
evalExpr env (ArrayLit []) = return $ (List [])
evalExpr env (ArrayLit l) = do
    a <- mapM (evalExpr env) l
    return $ (List a)
            
--Chamando função
evalExpr env (CallExpr exp (expr:l)) = do
    evalExpr env exp

--evalListRet env (List (x:xs)) (Id a) = do

evalStmt :: StateT -> Statement -> StateTransformer Value
evalStmt env EmptyStmt = return Nil
evalStmt env (VarDeclStmt []) = return Nil
evalStmt env (VarDeclStmt (decl:ds)) =
    varDecl env decl >> evalStmt env (VarDeclStmt ds)
evalStmt env (ExprStmt expr) = evalExpr env expr
---------------------------------------------------------------------------------------
------------------------------ If e else ---------------------------------------------
evalStmt env (IfStmt expr ifBlock elseBlock) = do
    ret <- evalExpr env expr
    case ret of
        (Bool b) -> if b then evalStmt env ifBlock else evalStmt env elseBlock
-------------------------------- blockStmt with break-------------------------------------------
evalStmt env (BlockStmt []) = return Nil
evalStmt env (BlockStmt (x:xs)) = do
    case x of
        (BreakStmt Nothing) -> return Break --- Break Function
        _ -> do
            evalStmt env x
            evalStmt env (BlockStmt xs)             
--------------------- If -----------------------------------------------------------
evalStmt env (IfSingleStmt expr ifBlock) = ST $ \state ->
    let 
        (ST a) = evalStmt env EmptyStmt
        (v,state1) = a state
        (ST b) = do
            ret <- evalExpr env expr
            case ret of 
                err@(Error s) -> return err
                Bool b ->if b == True then evalStmt env ifBlock else evalStmt env EmptyStmt  
        (result,locVar) = b state1             
        varGlob = intersection locVar state
    in (result,varGlob)   

             
------------------ For ----------------------------------------------------------
evalStmt env (ForStmt ini exp increments body) = do
    evalForInit env ini
    case exp of 
        (Just a) -> do 
            ret <- evalExpr env a
            case ret of
                (Bool b) -> if (b == True) then do
                                domingo <- evalStmt env body
                                case domingo of
                                    (Break) -> return Nil
                                    _ -> case increments of 
                                            (Just i) -> do
                                                evalExpr env i
                                                evalStmt env (ForStmt NoInit exp increments body)
                                            (Nothing) -> do
                                                evalStmt env EmptyStmt
                                                evalStmt env (ForStmt NoInit exp increments body)
                            else evalStmt env EmptyStmt
        (Nothing) -> do
            domingo <- evalStmt env body
            case domingo of
                (Break) -> return Nil
                _ -> case increments of 
                        (Just i) -> do
                            evalExpr env i
                            evalStmt env (ForStmt NoInit exp increments body)
                        (Nothing) -> do
                            evalStmt env EmptyStmt
                            evalStmt env (ForStmt NoInit exp increments body)
--Função
evalStmt env (FunctionStmt (Id ini) arg body) = do
    setVar ini (Function (Id ini) arg body) 

--    case ret of
--        (ReturnStmt a) -> evalStmt env a      
------------------------------------------------------------------------------------
----------------------------------Break----------------------------------------------

--evalstmt env (BreakStmt id) = ST $ \state ->
 --   let 
 --       (ST a) = evalStmt env EmptyStmt
--        (v,state1) = a state
 --       (ST b) = do
 --           case id of
 --               (Just i) -> do
 --           (result,locVar) = b state1
  --          varGlob = intersection locVar state
  --  in (result,varGlob)
  --              (Nothing) -> Nothing    

-------------------------------------------------------------------------------------
    
------------------ case ForInit ---------------------------------------------------

evalForInit env (NoInit) = evalStmt env EmptyStmt
evalForInit env (VarInit var) = (evalStmt env (VarDeclStmt var))    
evalForInit env (ExprInit exp) = evalExpr env exp 

-------------------------------------------------------------------------------------
-- Do not touch this one :)
evaluate :: StateT -> [Statement] -> StateTransformer Value
evaluate env [] = return Nil
evaluate env [stmt] = evalStmt env stmt
evaluate env (s:ss) = evalStmt env s >> evaluate env ss

--
-- Operators
--

infixOp :: StateT -> InfixOp -> Value -> Value -> StateTransformer Value
infixOp env OpAdd  (Int  v1) (Int  v2) = return $ Int  $ v1 + v2
infixOp env OpSub  (Int  v1) (Int  v2) = return $ Int  $ v1 - v2
infixOp env OpMul  (Int  v1) (Int  v2) = return $ Int  $ v1 * v2
infixOp env OpDiv  (Int  v1) (Int  v2) = return $ Int  $ div v1 v2
infixOp env OpMod  (Int  v1) (Int  v2) = return $ Int  $ mod v1 v2
infixOp env OpLT   (Int  v1) (Int  v2) = return $ Bool $ v1 < v2
infixOp env OpLEq  (Int  v1) (Int  v2) = return $ Bool $ v1 <= v2
infixOp env OpGT   (Int  v1) (Int  v2) = return $ Bool $ v1 > v2
infixOp env OpGEq  (Int  v1) (Int  v2) = return $ Bool $ v1 >= v2
infixOp env OpEq   (Int  v1) (Int  v2) = return $ Bool $ v1 == v2
infixOp env OpNEq  (Bool v1) (Bool v2) = return $ Bool $ v1 /= v2
infixOp env OpLAnd (Bool v1) (Bool v2) = return $ Bool $ v1 && v2
infixOp env OpLOr  (Bool v1) (Bool v2) = return $ Bool $ v1 || v2

infixOp env op (Var x) v2 = do
    var <- stateLookup env x
    case var of
        error@(Error _) -> return error
        val -> infixOp env op val v2

infixOp env op v1 (Var x) = do
    var <- stateLookup env x
    case var of
        error@(Error _) -> return error
        val -> infixOp env op v1 val

postfixOp env PostfixInc  (Int a) = return $ Int $ a + 1 
postfixOp env PostfixDec  (Int a) = return $ Int $ a - 1

--
-- Environment and auxiliary functions
--

environment :: Map String Value
environment = empty

stateLookup :: StateT -> String -> StateTransformer Value
stateLookup env var = ST $ \s ->
    (maybe
        (Error $ "Variable " ++ show var ++ " not defined")
        id
        (Map.lookup var (union s env)),
    s)

varDecl :: StateT -> VarDecl -> StateTransformer Value
varDecl env (VarDecl (Id id) maybeExpr) = do
    case maybeExpr of
        Nothing -> setVar id Nil
        (Just expr) -> do
            val <- evalExpr env expr
            setVar id val

setVar :: String -> Value -> StateTransformer Value
setVar var val = ST $ \s -> (val, insert var val s)

--
-- Types and boilerplate
--

type StateT = Map String Value
data StateTransformer t = ST (StateT -> (t, StateT))

instance Monad StateTransformer where
    return x = ST $ \s -> (x, s)
    (>>=) (ST m) f = ST $ \s ->
        let (v, newS) = m s
            (ST resF) = f v
        in resF newS

instance Functor StateTransformer where
    fmap = liftM

instance Applicative StateTransformer where
    pure = return
    (<*>) = ap

--
-- Main and results functions
--

showResult :: (Value, StateT) -> String
showResult (val, defs) = show val ++ "\n" ++ show (toList defs) ++ "\n"

getResult :: StateTransformer Value -> (Value, StateT)
getResult (ST f) = f empty

main :: IO ()
main = do
    js <- Parser.parseFromFile "Main.js"
    let statements = unJavaScript js
    putStrLn $ "AST: " ++ (show $ statements) ++ "\n"
    putStr $ showResult $ getResult $ evaluate environment statements
