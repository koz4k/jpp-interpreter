module Interpreter (interpret) where


import AbstractSyntax
import Error

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.ST.Trans
import Control.Monad.Trans.Writer
import Control.Monad.Except (ExceptT, runExceptT)
import qualified Control.Monad.Except as Except
import Control.Applicative

import Data.Functor
import Data.List
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Function
import qualified Data.Array as DArray


data Loc s = LVar (STRef s (Value s)) | LArrayElem (Array s) Integer
type Func s = [Value s] -> IM s (Value s)
type Array s = STArray s Integer (Value s)

data Value s = VVoid | VInt Integer | VBool Bool | VRef (Loc s) |
               VFunc (Func s) | VArray (Array s)

instance Show (Value s) where
  show v = case v of
    VInt i -> show i
    VBool True -> "true"
    VBool False -> "false"

type Env s = Map Ident (Loc s)
data ControlExc s = CBreak | CContinue | CReturn (Value s)
type IM s = ExceptT (ControlExc s)
                  (StateT (Env s) (STT s (WriterT (Endo String) ErrM)))


initEnv :: Env s
initEnv = Map.empty

getEnv :: IM s (Env s)
getEnv = lift get

putEnv :: Env s -> IM s ()
putEnv = lift . put

modifyEnv :: (Env s -> Env s) -> IM s ()
modifyEnv = lift . modify

newVar :: Ident -> Value s -> IM s ()
newVar ident val = do
  loc <- case val of
    VRef loc -> return loc
    _ -> LVar <$> (copy val >>= lift . lift . newSTRef)
  modifyEnv $ Map.insert ident loc

getIdent :: Ident -> IM s (Loc s)
getIdent ident = (Map.! ident) <$> getEnv

getLoc :: Loc s -> IM s (Value s)
getLoc (LVar ref) = lift . lift $ readSTRef ref
getLoc (LArrayElem arr i) = do
  let size = fromIntegral $ numElementsSTArray arr
  unless (0 <= i && i < size) .
    throwError $ "array index " ++ show i ++
                 " out of bounds; array size is " ++ show size
  lift . lift $ readSTArray arr i

setLoc :: Loc s -> Value s -> IM s ()
setLoc (LVar ref) = lift . lift . writeSTRef ref
setLoc (LArrayElem arr i) = lift . lift . writeSTArray arr i

makeArray :: [Value s] -> IM s (Array s)
makeArray vals = lift . lift . thawSTArray $
                   DArray.listArray (0, fromIntegral $ length vals - 1) vals

arrayToList :: Array s -> IM s [Value s]
arrayToList arr = DArray.elems <$> (lift . lift $ freezeSTArray arr)

copyArray :: Array s -> IM s (Array s)
copyArray arr = arrayToList arr >>= mapM copy >>= makeArray

showValue :: Value s -> IM s String
showValue v = value v >>= \v' -> case v' of
  VArray arr -> do
    strs <- arrayToList arr >>= mapM showValue
    return $ "[" ++ intercalate ", " strs ++ "]"
  _ -> return $ show v'

output :: String -> IM s ()
output str = lift . lift . lift . tell $ Endo (str ++)

outputValue :: Value s -> IM s ()
outputValue v = showValue v >>= output

value :: Value s -> IM s (Value s)
value (VRef loc) = getLoc loc
value v = return v

throwError :: ErrInfo -> IM s a
throwError = lift . lift . lift . lift . Except.throwError

throwControl :: ControlExc s -> IM s a
throwControl = Except.throwError

interpret :: Program -> ErrM String
interpret (Program stmts) =
    flip appEndo [] <$>
      execWriterT (runST (evalStateT (void . runExceptT $ execBlockTransp stmts)
                                     initEnv))

execBlockTransp :: [Stmt] -> IM s ()
execBlockTransp stmts = do
  e <- execBlock stmts $ return ()
  either throwControl return e

execBlock :: [Stmt] -> IM s () -> IM s (Either (ControlExc s) ())
execBlock stmts initM = do
  env <- getEnv
  lift . lift $ evalStateT (runExceptT $
                              initM >> sequence_ (execStmt <$> stmts)) env

execStmt :: Stmt -> IM s ()
execStmt x = case x of
  SExp exp -> void $ evalExp exp

  SAssign exp1 exp2 -> execAssign exp1 exp2
  SAddAssign exp1 exp2 -> execArithAssign (+) exp1 exp2
  SSubAssign exp1 exp2 -> execArithAssign (-) exp1 exp2
  SMulAssign exp1 exp2 -> execArithAssign (*) exp1 exp2
  SDivAssign exp1 exp2 -> execArithAssignM divM exp1 exp2

  SPass -> return ()
  SReturn -> throwControl $ CReturn VVoid
  SReturnVal exp -> evalExp exp >>= throwControl . CReturn
  SBreak -> throwControl CBreak
  SContinue -> throwControl CContinue

  SPrint exp -> do
    val <- evalExp exp
    outputValue val
    output "\n"

  SIf exp stmts elifs -> execIf exp stmts elifs []
  SIfElse exp stmts1 elifs stmts2 -> execIf exp stmts1 elifs stmts2
  SWhile exp stmts -> execWhile exp stmts

  SVarDef t ident exp -> evalExp exp >>= execVarDef t ident
  SFuncDef _ ident vds stmts -> void $ makeFunc (Just ident) vds stmts

execAssignOpM :: (Value s -> Value s -> IM s (Value s)) -> Exp -> Exp -> IM s ()
execAssignOpM f exp1 exp2 = do
      (VRef loc) <- evalExp exp1
      val1 <- getLoc loc
      val2 <- evalExpValue exp2
      f val1 val2 >>= setLoc loc

execAssign :: Exp -> Exp -> IM s ()
execAssign = execAssignOpM $ const copy

execArithAssignM :: (Integer -> Integer -> IM s Integer) ->
                    Exp -> Exp -> IM s ()
execArithAssignM f = execAssignOpM (\x y -> VInt <$> (f `on` intVal) x y)

execArithAssign :: (Integer -> Integer -> Integer) -> Exp -> Exp -> IM s ()
execArithAssign f = execArithAssignM $ liftRes2 f

copy :: Value s -> IM s (Value s)
copy (VArray arr) = VArray <$> copyArray arr
copy val = return val

execIf :: Exp -> [Stmt] -> [Elif] -> [Stmt] -> IM s ()
execIf exp stmts1 elifs stmts2 = execBranches branches
  where
    execBranches [] = return ()
    execBranches ((exp, stmts) : bs) = do
      b <- evalCond exp
      if b then execBlockTransp stmts
            else execBranches bs
    branches = (exp, stmts1) : map unpackElif elifs ++ [(ETrue, stmts2)]
    unpackElif (Elif exp stmts) = (exp, stmts)

execWhile :: Exp -> [Stmt] -> IM s ()
execWhile exp stmts = do
  b <- evalCond exp
  when b $ do
    e <- execBlock stmts $ return ()
    case e of
      Right () -> execWhile exp stmts
      Left CBreak -> return ()
      Left CContinue -> execWhile exp stmts
      Left (CReturn mv) -> throwControl $ CReturn mv

evalCond :: Exp -> IM s Bool
evalCond exp = boolVal <$> evalExpValue exp

evalExpValue :: Exp -> IM s (Value s)
evalExpValue exp = evalExp exp >>= value

evalExp :: Exp -> IM s (Value s)
evalExp exp = case exp of
  EInt integer -> return $ VInt integer
  ETrue -> return $ VBool True
  EFalse -> return $ VBool False

  EPlus exp -> evalExp exp
  EMinus exp -> VInt . negate <$> (intVal <$> evalExp exp)
  EAdd exp1 exp2 -> intIntOp (+) exp1 exp2
  ESub exp1 exp2 -> intIntOp (-) exp1 exp2
  EMul exp1 exp2 -> intIntOp (*) exp1 exp2
  EDiv exp1 exp2 -> opM intVal VInt divM exp1 exp2

  EEq exp1 exp2 -> VBool <$> eq exp1 exp2
  ENeq exp1 exp2 -> VBool . not <$> eq exp1 exp2
  ELt exp1 exp2 -> intBoolOp (<) exp1 exp2
  ELeq exp1 exp2 -> intBoolOp(<=) exp1 exp2
  EGt exp1 exp2 -> intBoolOp (>) exp1 exp2
  EGeq exp1 exp2 -> intBoolOp (>=) exp1 exp2

  ENot exp -> VBool . not <$> (boolVal <$> evalExp exp)
  EOr exp1 exp2 -> boolBoolOp (||) exp1 exp2
  EAnd exp1 exp2 -> boolBoolOp (&&) exp1 exp2

  EVar ident -> VRef <$> getIdent ident

  EArray exps -> VArray <$> (mapM evalExpValue exps >>= makeArray)
  EFill exp n -> VArray <$> do
    vals <- replicateM (fromIntegral n) $ evalExpValue exp
    makeArray vals
  EIndex exp1 exp2 -> do
    arrVal <- evalExp exp1
    VInt i <- evalExpValue exp2
    case arrVal of
      VRef loc -> do
        VArray arr <- getLoc loc
        return . VRef $ LArrayElem arr i
      VArray arr -> getLoc $ LArrayElem arr i

  ELambda _ vds exp -> VFunc <$> makeFunc Nothing vds [SReturnVal exp]
  ECall exp exps -> do
    VFunc f <- evalExpValue exp
    vals <- mapM evalExp exps
    f vals

divM :: Integer -> Integer -> IM s Integer
divM i1 i2 = if i2 /= 0 then return $ i1 `div` i2
                        else throwError "division by zero"

opM :: (Value s -> a) -> (b -> Value s) -> (a -> a -> IM s b) ->
        Exp -> Exp -> IM s (Value s)
opM vg vc f exp1 exp2 = vc <$> (liftArgs2 f `on` ve) exp1 exp2
  where ve exp = vg <$> evalExpValue exp

op :: (Value s -> a) -> (b -> Value s) -> (a -> a -> b) ->
      Exp -> Exp -> IM s (Value s)
op vg vc f = opM vg vc $ liftRes2 f

liftRes2 :: Monad m => (a -> b -> c) -> a -> b -> m c
liftRes2 f x y = return $ f x y

liftArgs2 :: (Monad m, Applicative m) => (a -> b -> m c) -> m a -> m b -> m c
liftArgs2 f m1 m2 = join $ f <$> m1 <*> m2

intIntOp :: (Integer -> Integer -> Integer) -> Exp -> Exp -> IM s (Value s)
intIntOp = op intVal VInt

intBoolOp :: (Integer -> Integer -> Bool) -> Exp -> Exp -> IM s (Value s)
intBoolOp = op intVal VBool

boolBoolOp :: (Bool -> Bool -> Bool) -> Exp -> Exp -> IM s (Value s)
boolBoolOp = op boolVal VBool

intVal :: Value s -> Integer
intVal (VInt i) = i

boolVal :: Value s -> Bool
boolVal (VBool b) = b

eq :: Exp -> Exp -> IM s Bool
eq exp1 exp2 = do
  v1 <- evalExpValue exp1
  v2 <- evalExpValue exp2
  valsEq v1 v2
  where
    valsEq v1 v2 = case (v1, v2) of
     (VInt i1, VInt i2) -> return $ i1 == i2
     (VBool b1, VBool b2) -> return $ b1 == b2
     (VArray arr1, VArray arr2) -> do
       vals1 <- arrayToList arr1
       vals2 <- arrayToList arr2
       and <$> zipWithM valsEq vals1 vals2

makeFunc :: Maybe Ident -> [VarDecl] -> [Stmt] -> IM s (Func s)
makeFunc mident vds stmts = do
  env <- getEnv
  let f vs = do
        e <- execBlock stmts $ do
          putEnv env
          def f
          forM_ (zip vds vs) $ \(VarDecl t ident, val) ->
            execVarDef t ident val
        case e of
          Left (CReturn v) -> return v
          Right () -> return VVoid
  def f
  return f
  where def f = maybe (return ()) (flip newVar $ VFunc f) mident

execVarDef :: Type -> Ident -> Value s -> IM s ()
execVarDef t ident val = do
  val' <- (if isRefType t then return else value) val
  newVar ident val'
