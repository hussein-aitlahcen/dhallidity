{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Use camelCase" #-}

module Lib (execute) where

import Control.Lens hiding (Const, Context)
import Control.Monad (foldM, guard, when)
import Control.Monad.Except (ExceptT (..), runExceptT, throwError)
import Control.Monad.State.Strict (MonadIO (liftIO), StateT (..))
import Control.Monad.Trans (lift)
import Data.Bifoldable (bitraverse_)
import Data.Bits (Bits (..))
import Data.DoubleWord (Word256 (Word256))
import Data.Either (either, fromRight)
import Data.Foldable (foldl', traverse_)
import Data.Functor.Identity (Identity (..))
import qualified Data.Map as M
import Data.Maybe (catMaybes, fromJust, fromMaybe)
import Data.Monoid (Sum (..))
import Data.Semigroup (Max (..))
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Data.Word (Word64)
import Dhall.Context (Context, empty, insert)
import Dhall.Core
  ( Const (..),
    Expr (..),
    FieldSelection (..),
    FunctionBinding (functionBindingAnnotation, functionBindingVariable),
    RecordField (..),
    Var (..),
    denote,
    makeRecordField,
    normalize,
  )
import Dhall.Import (load)
import Dhall.Map (fromList, toMap)
import Dhall.Parser (exprFromText)
import Dhall.Pretty (prettyExpr)
import qualified Dhall.TypeCheck as D (typeOf, typeWith)
import EVM.Opcode (Opcode (..), Opcode' (..), toHex, pattern DUP1)
import qualified EVM.Opcode as O
import EVM.Opcode.Internal (Ord16 (..))
import EVM.Opcode.Labelled (LabelledOpcode)
import qualified EVM.Opcode.Labelled as L
import qualified EVM.Opcode.Positional as P
import Numeric.Natural (Natural)

mAX_DYNAMIC_LOCALS :: Word256
mAX_DYNAMIC_LOCALS = 256

rESERVED_LOCALS :: Word256
rESERVED_LOCALS = 1

data CplVar = CplVar
  { _typ :: Expr Void Void,
    _memorySlot :: Word256
  }
  deriving stock (Eq, Show)

makeLenses ''CplVar

data CplState = CplState
  { _localBindings :: M.Map Text CplVar,
    _nextLabel :: Int,
    _memorySlotNext :: Word256
  }
  deriving stock (Eq, Show)

makeLenses ''CplState

execute :: IO ()
execute = do
  {- Resulting hex bytecode can be decompiled on https://ethervm.io/decompile -}
  -- Parse + Resolve imports
  program <-
    traverse
      load
      ( exprFromText
          "program"
          "let Message = < SetValue: Natural | ResetValue > \
          \ in merge \
          \ { SetValue = \\(x: Natural) -> env.sstore Natural x 0 \
          \ , ResetValue = env.sstore Natural 0 0 \
          \ } \
          \ (env.callDataLoad Message)"
      )
  bitraverse_
    print
    ( ( \validProgram ->
          bitraverse_
            print
            ( \programType ->
                if fromRight (error "typechecked; qed;") (D.typeOf @Void programType) /= Const Type
                  then error "must be type; sorry bro; qed;"
                  else go programType validProgram
            )
            (D.typeWith initialContext validProgram)
      )
        . denote
    )
    program
  where
    go :: Expr Void Void -> Expr Void Void -> IO ()
    go programType validProgram = do
      putStrLn ""
      putStrLn "<<==========>>"
      putStrLn "<<== TYPE ==>>"
      putStrLn "<<==========>>"
      putStrLn ""
      print $ prettyExpr programType
      putStrLn ""
      putStrLn "<<==========>>"
      putStrLn "<<== BASE ==>>"
      putStrLn "<<==========>>"
      putStrLn ""
      print $ prettyExpr validProgram
      putStrLn ""
      putStrLn "<<================>>"
      putStrLn "<<== NORMALIZED ==>>"
      putStrLn "<<================>>"
      putStrLn ""
      let normalized :: Expr Void Void
          !normalized = normalize validProgram
      print $ prettyExpr normalized
      putStrLn ""
      putStrLn "<<========================>>"
      putStrLn "<<== ABSTRACT BYTECODES ==>>"
      putStrLn "<<========================>>"
      putStrLn ""
      putStrLn ">> Compiling..."
      (compiled, _) <-
        either (error . show) id
          <$> runExceptT (runStateT (compile normalized) (CplState mempty 0 rESERVED_LOCALS))
      putStrLn ">> Compilation done."
      print $ ">> Bytecode: " <> show compiled
      putStrLn ""
      putStrLn "<<===================>>"
      putStrLn "<<== HEX BYTECODES ==>>"
      putStrLn "<<===================>>"
      putStrLn ""
      putStrLn $
        toHex $
          P.translate $
            fromRight (error "impossible; qed;") $
              L.translate $ [push $ 32 * mAX_DYNAMIC_LOCALS, PUSH 0x00, MSTORE] <> compiled <> [STOP]

class Builtin a where
  typeOf :: a -> Expr Void Void
  bindingOf :: a -> Text

class Builtin a => BuiltinType a where
  referTo :: a -> Expr Void Void
  referTo x = Var (V (bindingOf x) 0)

class BuiltinOpcode a where
  opcode :: a -> [LabelledOpcode]

data BuiltinAddress = BuiltinAddress

instance Builtin BuiltinAddress where
  typeOf _ = Const Type
  bindingOf _ = "Address"

instance BuiltinType BuiltinAddress

data BuiltinValue
  = CallValue
  | CallDataSize
  | CodeSize
  | GasPrice
  | ReturnDataSize
  | Coinbase
  | Timestamp
  | Number
  | Difficulty
  | GasLimit
  | ChainId
  | SelfBalance
  | BaseFee
  | ProgramCounter
  | MSize
  | Gas
  | Address
  | Origin
  | Caller
  | BalanceOf
  | MLoad
  | MStore
  | CallDataLoad
  | CallDataCopy
  | SLoad
  | SStore
  deriving (Enum, Bounded)

instance Builtin BuiltinValue where
  typeOf CallValue = Natural
  typeOf CallDataSize = Natural
  typeOf CodeSize = Natural
  typeOf GasPrice = Natural
  typeOf ReturnDataSize = Natural
  typeOf Coinbase = referTo BuiltinAddress
  typeOf Timestamp = Natural
  typeOf Number = Natural
  typeOf Difficulty = Natural
  typeOf GasLimit = Natural
  typeOf ChainId = Natural
  typeOf SelfBalance = Natural
  typeOf BaseFee = Natural
  typeOf ProgramCounter = Natural
  typeOf MSize = Natural
  typeOf Gas = Natural
  typeOf Address = referTo BuiltinAddress
  typeOf Origin = referTo BuiltinAddress
  typeOf Caller = referTo BuiltinAddress
  typeOf BalanceOf = Pi Nothing "_" (referTo BuiltinAddress) Natural
  typeOf MLoad = Pi Nothing "T" (Const Type) $ Pi Nothing "_" Natural $ Var $ V "T" 0
  typeOf MStore = Pi Nothing "T" (Const Type) $ Pi Nothing "_" (Var $ V "T" 0) $ Pi Nothing "_" Natural Natural
  typeOf CallDataLoad = Pi Nothing "T" (Const Type) $ Var $ V "T" 0
  typeOf CallDataCopy = Pi Nothing "_" Natural $ Pi Nothing "_" Natural $ Pi Nothing "_" Natural $ Record mempty
  typeOf SLoad = Pi Nothing "T" (Const Type) $ Pi Nothing "_" Natural $ Var $ V "T" 0
  typeOf SStore = Pi Nothing "T" (Const Type) $ Pi Nothing "_" (Var $ V "T" 0) $ Pi Nothing "_" Natural Natural

  bindingOf CallValue = "callValue"
  bindingOf CallDataSize = "callDataSize"
  bindingOf CodeSize = "codeSize"
  bindingOf GasPrice = "gasPrice"
  bindingOf ReturnDataSize = "returnDataSize"
  bindingOf Coinbase = "coinbase"
  bindingOf Timestamp = "timestamp"
  bindingOf Number = "number"
  bindingOf Difficulty = "difficulty"
  bindingOf GasLimit = "gasLimit"
  bindingOf ChainId = "chainId"
  bindingOf SelfBalance = "selfBalance"
  bindingOf BaseFee = "baseFee"
  bindingOf ProgramCounter = "pc"
  bindingOf MSize = "msize"
  bindingOf Gas = "gas"
  bindingOf Address = "address"
  bindingOf Origin = "origin"
  bindingOf Caller = "caller"
  bindingOf BalanceOf = "balanceOf"
  bindingOf MLoad = "mload"
  bindingOf MStore = "mstore"
  bindingOf CallDataLoad = "callDataLoad"
  bindingOf CallDataCopy = "callDataCopy"
  bindingOf SLoad = "sload"
  bindingOf SStore = "sstore"

instance BuiltinOpcode BuiltinValue where
  opcode CallValue = [CALLVALUE]
  opcode CallDataSize = [CALLDATASIZE]
  opcode CodeSize = [CODESIZE]
  opcode GasPrice = [GASPRICE]
  opcode ReturnDataSize = [RETURNDATASIZE]
  opcode Coinbase = [COINBASE]
  opcode Timestamp = [TIMESTAMP]
  opcode Number = [NUMBER]
  opcode Difficulty = [DIFFICULTY]
  opcode GasLimit = [GASLIMIT]
  opcode ChainId = [CHAINID]
  opcode SelfBalance = [SELFBALANCE]
  opcode BaseFee = [BASEFEE]
  opcode ProgramCounter = [PC]
  opcode MSize = [MSIZE]
  opcode Gas = [GAS]
  opcode Address = [ADDRESS]
  opcode Origin = [ORIGIN]
  opcode Caller = [CALLER]
  opcode BalanceOf = [BALANCE]
  opcode MLoad = [MLOAD]
  opcode MStore = [MSTORE]
  opcode CallDataLoad = [CALLDATALOAD]
  opcode CallDataCopy = [CALLDATACOPY]
  opcode SLoad = [SLOAD]
  opcode SStore = [SSTORE]

builtinOpcodes :: M.Map Text [LabelledOpcode]
builtinOpcodes =
  M.fromList $
    (\x -> (bindingOf x, opcode x))
      <$> [ minBound @BuiltinValue
            .. maxBound @BuiltinValue
          ]

initialContext :: Context (Expr Void Void)
initialContext =
  collapse
    [ (bindingOf BuiltinAddress, typeOf BuiltinAddress),
      ( "env",
        Record $
          fromList $
            mkEntry
              <$> [ minBound @BuiltinValue
                    .. maxBound @BuiltinValue
                  ]
      )
    ]
  where
    mkEntry x = (bindingOf x, makeRecordField $ typeOf x)
    collapse = foldl' (\z (x, y) -> insert x y z) empty

-- Natural is infinite in Haskell, basically a BigInt
maxWord256 :: Natural
maxWord256 = fromIntegral $ maxBound @Word256

sizeOf :: Monad m => Expr Void Void -> ExceptT String m Word256
sizeOf Natural = pure 32
sizeOf (Union fields) = do
  (+ 32) . maximum <$> traverse sizeOf (catMaybes $ M.elems $ toMap fields)
sizeOf (Record fields) = do
  sizes <- traverse (sizeOf . recordFieldValue) $ M.elems $ toMap fields
  pure $ getSum $ foldMap Sum sizes
sizeOf x = throwError $ "Not sizeable: " <> show x

offsetOf :: Monad m => Text -> Expr Void Void -> ExceptT String m Word256
offsetOf _ (Union _) = pure 32
offsetOf field (Record fields) = do
  let fields' = toMap fields
      index = M.findIndex field fields'
  sizeOf (Record $ fromList $ take index $ M.toList fields')
offsetOf _ x = throwError $ "Not offsetable: " <> show x

getType :: Expr Void Void -> StateT CplState (ExceptT String IO) (Expr Void Void)
getType x = do
  extraContext <- use localBindings
  let context = M.foldrWithKey insert initialContext (view typ <$> extraContext)
  pure $ fromRight "typechecked; qed;" $ D.typeWith context x

compile :: Expr Void Void -> StateT CplState (ExceptT String IO) [LabelledOpcode]
compile = doCompile
  where
    doCompile :: Expr Void Void -> StateT CplState (ExceptT String IO) [LabelledOpcode]
    doCompile (NaturalLit x)
      | x <= maxWord256 = pure [push x]
    doCompile (IntegerLit x)
      | x <= fromIntegral maxWord256 = pure [push x]
    doCompile (NaturalPlus x y) = do
      p <- doCompile y
      q <- doCompile x
      pure $ p <> q <> [ADD]
    doCompile (App (App NaturalSubtract x) y) = do
      p <- doCompile y
      q <- doCompile x
      pure $ p <> q <> [SUB]
    doCompile (Field (Var (V "env" _)) (FieldSelection _ builtin _))
      | M.member builtin builtinOpcodes =
        pure $ fromMaybe (error "member; qed;") $ builtinOpcodes M.!? builtin
    -- Builtin env.mstore
    doCompile (App (App (App (Field (Var (V "env" _)) (FieldSelection _ builtin _)) typeExpr) valueExpr) offsetExpr)
      | builtin == bindingOf MStore = do
        size <- (`div` 32) <$> lift (sizeOf typeExpr)
        value <- doCompile valueExpr
        offset <- doCompile offsetExpr
        pure $ value <> ((\x -> offset <> [push $ (x + 1) * 32, push $ size * 32, SUB, ADD, MSTORE]) =<< [0 .. size - 1]) <> offset
    -- Builtin env.mload
    doCompile (App (App (Field (Var (V "env" _)) (FieldSelection _ builtin _)) typeExpr) offsetExpr)
      | builtin == bindingOf MLoad = do
        size <- (`div` 32) <$> lift (sizeOf typeExpr)
        offset <- doCompile offsetExpr
        pure $ (\x -> offset <> [push $ x * 32, ADD, MLOAD]) =<< [0 .. size - 1]
    -- Builtin env.sstore
    doCompile (App (App (App (Field (Var (V "env" _)) (FieldSelection _ builtin _)) typeExpr) valueExpr) offsetExpr)
      | builtin == bindingOf SStore = do
        size <- (`div` 32) <$> lift (sizeOf typeExpr)
        value <- doCompile valueExpr
        offset <- doCompile offsetExpr
        pure $ value <> ((\x -> offset <> [push $ x + 1, push size, SUB, ADD, SSTORE]) =<< [0 .. size - 1]) <> offset
    -- Builtin env.sload
    doCompile (App (App (Field (Var (V "env" _)) (FieldSelection _ builtin _)) typeExpr) offsetExpr)
      | builtin == bindingOf SLoad = do
        size <- (`div` 32) <$> lift (sizeOf typeExpr)
        offset <- doCompile offsetExpr
        pure $ (\x -> offset <> [push x, ADD, SLOAD]) =<< [0 .. size - 1]
    -- Builtin env.callDataLoad
    doCompile (App (Field (Var (V "env" _)) (FieldSelection _ builtin _)) typeExpr)
      | builtin == bindingOf CallDataLoad = do
        size <- (`div` 32) <$> lift (sizeOf typeExpr)
        pure $ (\x -> [push $ x * 32, CALLDATALOAD]) =<< [0 .. size - 1]
    -- Builtin env.<trivialUnaryFunction>
    doCompile (App (Field (Var (V "env" _)) (FieldSelection _ builtin _)) x)
      | M.member builtin builtinOpcodes = do
        p <- doCompile x
        pure $ p <> fromMaybe (error "member; qed;") (builtinOpcodes M.!? builtin)
    doCompile (App x y) = do
      p <- doCompile y
      q <- doCompile x
      pure $ p <> q
    doCompile (Field x (FieldSelection _ y _)) = do
      tyX <- getType x
      case (tyX, x) of
        (Const Type, ty@(Union fields)) -> do
          let fields' = toMap fields
              index = M.findIndex y fields'
          size <- (`div` 32) <$> lift (sizeOf x)
          variantSize <- case fields' M.! y of
            Just field -> (`div` 32) <$> lift (sizeOf field)
            Nothing -> pure 0
          liftIO $ print "Union"
          liftIO $ print variantSize
          liftIO $ print size
          liftIO $ print x
          pure $ replicate (fromIntegral $ size - variantSize - 1) (push 0) <> [push index]
        (ty@(Record fields), _) -> do
          let (RecordField _ fieldTy _ _) = toMap fields M.! y
          offset <- (`div` 32) <$> lift (offsetOf y ty)
          size <- (`div` 32) <$> lift (sizeOf ty)
          fieldSize <- (`div` 32) <$> lift (sizeOf fieldTy)
          let stackMax = size
              fieldStackStart = size - offset - 1
              fieldStackEnd = fieldStackStart - fieldSize + 1
              tail = stackMax - fieldStackEnd - fieldSize
          liftIO $ putStrLn "==============="
          liftIO $ print $ "Size: " <> show size
          liftIO $ print $ "FieldSize: " <> show fieldSize
          liftIO $ print $ "Offset: " <> show offset
          liftIO $ print $ "Tail: " <> show tail
          liftIO $
            putStrLn $
              "Selecting " <> T.unpack y
                <> " of type "
                <> show (prettyExpr fieldTy)
                <> " at offset "
                <> show offset
                <> " in "
                <> show (prettyExpr ty)
          p <- doCompile x
          let storeTemp i = [push $ (fieldSize - i - 1) * 32] <> mload 0x00 <> [ADD, MSTORE]
              restoreTemp i = [push $ i * 32] <> mload 0x00 <> [ADD, MLOAD]
          pure $
            p
              <> replicate (fromIntegral fieldStackEnd) POP
              <> (storeTemp =<< [0 .. fieldSize - 1])
              <> replicate (fromIntegral tail) POP
              <> (restoreTemp =<< [0 .. fieldSize - 1])
        x -> error $ show x
    doCompile (RecordLit fields) = do
      mconcat . M.elems <$> traverse (doCompile . recordFieldValue) (toMap fields)
    doCompile (Merge (RecordLit fields) unionExpr c) = do
      liftIO $ print fields
      p <- compile unionExpr
      unionType <- getType unionExpr
      unionSize <- (`div` 32) <$> lift (sizeOf unionType)
      let fields' = M.elems $ toMap fields
      (_, q) <-
        foldM
          ( \(i, fallback) caseExpr -> do
              match <- compile caseExpr
              label <- use nextLabel
              nextLabel += 1
              variantSize <- case fields' !! i of
                RecordField _ (Lam _ binding _) _ _ ->
                  (`div` 32) <$> lift (sizeOf $ functionBindingAnnotation binding)
                _ -> pure 0
              liftIO $ print $ "Size: " <> show unionSize <> ", Variant: " <> show variantSize
              pure
                ( i + 1,
                  iff
                    label
                    [DUP1, push i, O.EQ]
                    -- pop the tag and padding as we wipe the union when matching
                    (replicate (fromIntegral $ unionSize - variantSize) POP <> match)
                    fallback
                )
          )
          (0, [push 0, push 0, REVERT])
          (recordFieldValue <$> fields')
      pure $ p <> q
    doCompile (Lam c binding body) = do
      let ann = functionBindingAnnotation binding
          var = functionBindingVariable binding
      size <- (`div` 32) <$> lift (sizeOf ann)
      slot <- use memorySlotNext
      memorySlotNext += size
      when
        (slot + size > mAX_DYNAMIC_LOCALS)
        (throwError "Ser, memory has limits...")
      liftIO $ putStrLn "==============="
      liftIO $ print $ "ValueType: " <> prettyExpr ann
      liftIO $ print $ "Slot: " <> show slot
      localBindings %= M.insert var (CplVar ann slot)
      -- store
      p <-
        compile
          ( App
              ( App
                  ( App
                      ( Field
                          (Var (V "env" 0))
                          (FieldSelection Nothing (bindingOf MStore) Nothing)
                      )
                      ann
                  )
                  -- already on the stack
                  (RecordLit mempty)
              )
              (NaturalLit (fromIntegral $ slot * 32))
          )
      -- alpha normalize with slot ref
      q <-
        compile $
          normalize $
            App
              (Lam c binding body)
              ( App
                  ( App
                      ( Field
                          (Var (V "env" 0))
                          (FieldSelection Nothing (bindingOf MLoad) Nothing)
                      )
                      ann
                  )
                  (NaturalLit (fromIntegral $ slot * 32))
              )
      localBindings %= M.delete var
      -- trick: pop the returned offset
      pure $ p <> (POP : q)
    doCompile (Union _) = pure []
    doCompile (Record _) = pure []
    doCompile x = error $ "Ser, everything has limits... " <> show x

freepointer :: [LabelledOpcode]
freepointer = [push 0x00, MLOAD]

push :: Integral a => a -> LabelledOpcode
push = PUSH . fromIntegral

mload :: Word256 -> [LabelledOpcode]
mload offset = [PUSH offset, MLOAD]

mstore :: Word256 -> Word256 -> [LabelledOpcode]
mstore value offset = [PUSH value, PUSH offset, MSTORE]

mstore8 :: Word256 -> Word256 -> [LabelledOpcode]
mstore8 value offset = [PUSH value, PUSH offset, MSTORE]

sload :: Word256 -> [LabelledOpcode]
sload key = [PUSH key, SLOAD]

sstore :: Word256 -> Word256 -> [LabelledOpcode]
sstore key value = [PUSH value, PUSH key, SSTORE]

iff :: Int -> [LabelledOpcode] -> [LabelledOpcode] -> [LabelledOpcode] -> [LabelledOpcode]
iff nb cond true false =
  let labelSuffix = "_" <> T.pack (show nb)
   in cond
        <> [JUMPI $ "true" <> labelSuffix]
        <> false
        <> [JUMP $ "end" <> labelSuffix, JUMPDEST $ "true" <> labelSuffix]
        <> true
        <> [JUMPDEST $ "end" <> labelSuffix]
