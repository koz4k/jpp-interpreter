module StaticCheck (staticCheck) where


import AbstractSyntax
import Error
import Print

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Reader
import Control.Monad.Except
import Control.Applicative

import Data.Functor
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.List


type TypeEnv = Map Ident Type
data SCS = SCS { env :: TypeEnv
               , insideLoop :: Bool
               , returnType :: Maybe Type
               , returned :: Bool
               }
type SCM = StateT SCS ErrM

initState :: SCS
initState = SCS Map.empty False Nothing False

modifyEnv :: (TypeEnv -> TypeEnv) -> SCS -> SCS
modifyEnv f = SCS <$> (f . env) <*> insideLoop <*> returnType <*> returned

setInsideLoop :: Bool -> SCS -> SCS
setInsideLoop il = SCS <$> env <*> const il <*> returnType <*> returned

setReturnType :: Maybe Type -> SCS -> SCS
setReturnType mrt = SCS <$> env <*> insideLoop <*> const mrt <*> returned

setReturned :: Bool -> SCS -> SCS
setReturned ret = SCS <$> env <*> insideLoop <*> returnType <*> const ret

staticCheck :: Program -> ErrM ()
staticCheck (Program stmts) = evalStateT (void $ checkBlock stmts id) initState
  where
    checkBlock :: [Stmt] -> (SCS -> SCS) -> SCM Bool
    checkBlock stmts mod = do
      is <- mod <$> get
      lift $ returned <$> execStateT (sequence_ $ checkStmt <$> stmts) is

    checkStmt :: Stmt -> SCM ()
    checkStmt x = case x of
      SExp exp -> void $ getType exp

      SAssign exp1 exp2 -> checkAssign exp1 exp2
      SAddAssign exp1 exp2 -> checkArithAssign exp1 exp2
      SSubAssign exp1 exp2 -> checkArithAssign exp1 exp2
      SMulAssign exp1 exp2 -> checkArithAssign exp1 exp2
      SDivAssign exp1 exp2 -> checkArithAssign exp1 exp2

      SPass -> return ()
      SReturn -> checkCanReturn TVoid
      SReturnVal exp -> do
        t <- getType exp
        checkCanReturn t
        modify $ setReturned True
      SBreak -> checkInsideLoop "break"
      SContinue -> checkInsideLoop "continue"

      SPrint exp -> do
        t <- getType exp
        unless (isDataType t) . throwError $ "cannot print " ++ printTree t

      SIf exp stmts elifs -> do
        void $ checkCond exp stmts
        void $ checkElifs elifs
      SIfElse exp stmts1 elifs stmts2 -> do
        ret1 <- checkCond exp stmts1
        ret2 <- checkElifs elifs
        ret3 <- checkBlock stmts2 id
        when (ret1 && ret2 && ret3) . modify $ setReturned True
      SWhile exp stmts -> do
        checkExpType TBool exp
        void . checkBlock stmts $ setInsideLoop True

      SVarDef t ident exp -> do
        lift $ checkTypeValid t
        act <- getType exp
        lift $ checkTypesInitializable t act
        modify . modifyEnv . Map.insert ident $ valueType t
      SFuncDef rt ident vds stmts -> do
        (ft, vars) <- lift $ processFuncSig rt vds
        modify . modifyEnv $ Map.insert ident ft
        ret <- checkBlock stmts ((modifyEnv . Map.union $ Map.fromList vars) .
                                 setInsideLoop False . setReturnType (Just rt))
        when (rt /= TVoid && not ret) $
          throwError "a function returning non-void must always return"

    checkAssign exp1 exp2 = do
      t1 <- getType exp1
      unless (isRefType t1) . throwError $ "expression on the left side " ++
        "of an assignment must be a reference, got " ++ printTree t1 ++
        " instead"
      checkExpType t1 exp2

    checkArithAssign exp1 exp2 = checkExpType TInt exp1 >> checkAssign exp1 exp2

    checkCond exp stmts = checkExpType TBool exp >> checkBlock stmts id

    checkElifs elifs = and <$> sequence (checkElif <$> elifs)
    checkElif (Elif exp stmts) = checkCond exp stmts

    checkExpType t exp = do
      act <- getType exp
      lift $ checkTypesCompatible t act

    checkCanReturn :: Type -> SCM ()
    checkCanReturn t = do
      mrt <- gets returnType
      when (isNothing mrt) $ throwError "cannot use return outside of a function"
      lift $ checkTypesInitializable (fromJust mrt) t

    checkInsideLoop :: String -> SCM ()
    checkInsideLoop instr = do
      il <- gets insideLoop
      unless il . throwError $ "cannot use " ++ instr ++ " outside of a loop"

    getType exp = env <$> get >>= lift . getExpType exp

getExpType :: Exp -> TypeEnv -> ErrM Type
getExpType exp = runReaderT $ getType exp
  where
    getType :: Exp -> ReaderT TypeEnv ErrM Type
    getType exp = case exp of

      EInt integer -> return TInt
      ETrue -> return TBool
      EFalse -> return TBool

      EPlus exp -> typedUnOp TInt exp
      EMinus exp -> typedUnOp TInt exp
      EAdd exp1 exp2 -> typedBinOp TInt exp1 exp2
      ESub exp1 exp2 -> typedBinOp TInt exp1 exp2
      EMul exp1 exp2 -> typedBinOp TInt exp1 exp2
      EDiv exp1 exp2 -> typedBinOp TInt exp1 exp2

      EEq exp1 exp2 -> eqOp exp1 exp2
      ENeq exp1 exp2 -> eqOp exp1 exp2
      ELt exp1 exp2 -> cmpOp exp1 exp2
      ELeq exp1 exp2 -> cmpOp exp1 exp2
      EGt exp1 exp2 -> cmpOp exp1 exp2
      EGeq exp1 exp2 -> cmpOp exp1 exp2

      ENot exp -> typedUnOp TBool exp
      EOr exp1 exp2 -> typedBinOp TBool exp1 exp2
      EAnd exp1 exp2 -> typedBinOp TBool exp1 exp2

      EVar ident -> do
        r <- reader $ Map.lookup ident
        case r of
          Just t -> return . TRef $ valueType t
          Nothing -> throwError $ "undefined identifier " ++ printTree ident

      EArray [] -> throwError "invalid array size: 0"
      EArray (exp : exps) -> do
        t <- valueType <$> getType exp
        sequence_ $ checkTypeIs t <$> exps
        return . TArray t $ 1 + fromIntegral (length exps)

      EFill exp n
        | n > 0     -> flip TArray n . valueType <$> getType exp
        | otherwise -> throwError $ "invalid array size: " ++ show n

      EIndex exp1 exp2 -> do
        checkTypeIs TInt exp2
        t <- getType exp1
        case t of
          TArray t' _ -> return t'
          TRef (TArray t' _) -> return $ TRef t'
          t' -> throwError $ "type " ++ printTree t' ++ " is not an array"

      ELambda rt vds exp -> do
        (ft, vars) <- lift $ processFuncSig rt vds
        local (Map.union $ Map.fromList vars) $
              checkTypeIs rt exp
        return ft

      ECall exp exps -> do
        t <- getType exp
        case valueType t of
          TFunc rt ats -> do
            let (lexps, lats) = (length exps, length ats)
            unless (lexps == lats) .
                   throwError $ "invalid number of function arguments; " ++
                                "expected " ++ show lats ++ ", got " ++
                                show lexps
            zipWithM_ cti ats exps
            return rt
              where cti t exp = getType exp >>= lift . checkTypesInitializable t
          _ -> throwError $ "type " ++ printTree t ++ " is not a function"

    typedUnOp t exp = checkTypeIs t exp >> return (valueType t)

    typedBinOp t exp1 exp2 = do
      checkTypeIs t exp1
      checkTypeIs t exp2
      return $ valueType t

    eqOp exp1 exp2 = do
      t1 <- valueType <$> getType exp1
      checkTypeIs t1 exp2
      unless (isDataType t1) .
             throwError $ "cannot compare " ++ printTree t1 ++ " for equality"
      return TBool

    cmpOp exp1 exp2 = do
      checkTypeIs TInt exp1
      checkTypeIs TInt exp2
      return TBool

    checkTypeIs t exp = getType exp >>= lift . checkTypesCompatible t

checkTypeValid :: Type -> ErrM ()
checkTypeValid t = case t of
  TVoid -> throwError "invalid type: void"
  TRef (TRef _) -> throwError "invalid type: nested reference"
  TRef t' -> checkTypeValid t'
  TArray (TRef _) _ -> throwError "invalid type: array of references"
  TArray et n
    | n > 0 -> checkTypeValid et
    | otherwise -> throwError $ "invalid array size: " ++ show n
  TFunc rt ats -> checkReturnTypeValid rt >> sequence_ (checkTypeValid <$> ats)
  _ -> return ()

checkReturnTypeValid :: Type -> ErrM ()
checkReturnTypeValid t = case t of
  TVoid -> return ()
  TRef TVoid -> throwError "invalid type: reference to void"
  _ -> checkTypeValid t

processFuncSig :: Type -> [VarDecl] -> ErrM (Type, [(Ident, Type)])
processFuncSig rt vds = do
  checkReturnTypeValid rt
  vars <- forM vds (\(VarDecl t i) -> do
    checkTypeValid t
    return (i, t))
  when ((length . nub $ map fst vars) /= length vars) $
       throwError "duplicate function argument names"
  return (TFunc rt $ snd <$> vars, vars)

checkTypesCompatible :: Type -> Type -> ErrM ()
checkTypesCompatible t act =
  unless (typesCompatible t act) .
          throwError $ "incompatible types; expected " ++ printTree t ++
                      ", got " ++ printTree act

checkTypesInitializable :: Type -> Type -> ErrM ()
checkTypesInitializable t act = do
  when (isRefType t && not (isRefType act)) $
        throwError $ "cannot initialize a reference " ++ printTree t ++
                    " with a non-reference " ++ printTree act
  checkTypesCompatible t act

isDataType :: Type -> Bool
isDataType t = case t of
  TVoid       -> False
  TInt        -> True
  TBool       -> True
  TArray t' _ -> isDataType t'
  TFunc _ _   -> False
  TRef t'     -> isDataType t'

typesCompatible :: Type -> Type -> Bool
typesCompatible x y = valueType x == valueType y

valueType :: Type -> Type
valueType (TRef t) = t
valueType t = t
