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

module Lib (execute) where

import Control.Lens hiding (Const, Context)
import Control.Monad.State.Strict (MonadIO (liftIO), StateT (..))
import Data.Bifoldable (bitraverse_)
import Data.Bits (Bits (..))
import Data.DoubleWord (Word256 (Word256))
import Data.Either (either, fromRight)
import Data.Foldable (foldl', traverse_)
import Data.Functor.Identity (Identity (..))
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Monoid (Sum (..))
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Data.Word (Word64)
import Debug.Trace (traceShowId)
import Dhall.Context (Context, empty, insert)
import Dhall.Core
  ( Const (..),
    Expr (..),
    FieldSelection (..),
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
import EVM.Opcode.Internal (Ord16 (..))
import Numeric.Natural (Natural)

data CplState = CplState
  { _memoryPointer :: Word256,
    _bindingPointer :: M.Map Text Word256
  }
  deriving stock (Eq, Show)

makeLenses ''CplState

execute :: IO ()
execute = do
  {- This program compiles to 0x303162079f2c01470100
     Resulting hex bytecode can be decompiled on https://ethervm.io/decompile

     contract Contract {
         function main() {
             var var0 = address(this).balance + address(this).balance + 0x079f2c;
             stop();
         }
     }
  -}
  -- Parse + Resolve imports
  program <-
    traverse
      load
      ( exprFromText
          "program"
          "let T = { q: Natural, x: Natural, y: { a: Natural, b: Natural } , z: Natural } in \
          \let value: T = env.mload T (env.mload Natural 0x40) \
          \in env.mload T (env.mstore T { q = 0xCAFE, x = 0xBABE, y = { a = 0xDEAD, b = 0xC0DE }, z = 0xBEEF } (env.mload Natural 0x40))"
      )
  bitraverse_
    print
    ( ( \validProgram ->
          bitraverse_
            print
            (\programType -> go programType validProgram)
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
      print $ prettyExpr $ denote @_ @_ @Void validProgram
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
      (compiled, _) <- runStateT (compile normalized) (CplState 0 mempty)
      putStrLn ">> Compilation done."
      print $ ">> Bytecode: " <> show compiled
      putStrLn ""
      putStrLn "<<===================>>"
      putStrLn "<<== HEX BYTECODES ==>>"
      putStrLn "<<===================>>"
      putStrLn ""
      putStrLn $ toHex $ [PUSH 0x60, PUSH 0x40, MSTORE] <> compiled <> [STOP]

class Builtin a where
  typeOf :: a -> Expr Void Void
  bindingOf :: a -> Text

class Builtin a => BuiltinType a where
  referTo :: a -> Expr Void Void
  referTo x = Var (V (bindingOf x) 0)

class BuiltinOpcode a where
  opcode :: a -> [Opcode]

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
  typeOf CallDataLoad = Pi Nothing "_" Natural Natural
  typeOf CallDataCopy = Pi Nothing "_" Natural $ Pi Nothing "_" Natural $ Pi Nothing "_" Natural $ Record mempty

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

builtinOpcodes :: M.Map Text [Opcode]
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

sizeOf :: Expr Void Void -> Either String Word256
sizeOf Natural = Right 32
sizeOf (Record fields) = do
  sizes <- traverse (sizeOf . recordFieldValue) (M.elems $ toMap fields)
  pure $ getSum $ foldMap Sum sizes
sizeOf x = Left $ "Not sizeable: " <> show x

offsetOf :: Text -> Expr Void Void -> Either String Word256
offsetOf field (Record fields) = do
  let fields' = toMap fields
      index = M.findIndex field fields'
  sizeOf (Record $ fromList $ take index $ M.toList fields')
offsetOf _ x = Left $ "Not offsetable: " <> show x

compile :: Expr Void Void -> StateT CplState IO [Opcode]
compile (NaturalLit x)
  | x <= maxWord256 = pure [push x]
compile (IntegerLit x)
  | x <= fromIntegral maxWord256 = pure [push x]
compile (NaturalPlus x y) = do
  p <- compile y
  q <- compile x
  pure $ p <> q <> [ADD]
compile (App (App NaturalSubtract x) y) = do
  p <- compile y
  q <- compile x
  pure $ p <> q <> [SUB]
compile (Field (Var (V "env" _)) (FieldSelection _ builtin _))
  | M.member builtin builtinOpcodes =
    pure $ fromMaybe (error "member; qed;") $ builtinOpcodes M.!? builtin
-- Builtin env.mstore
compile (App (App (App (Field (Var (V "env" _)) (FieldSelection _ builtin _)) typeExpr) valueExpr) offsetExpr)
  | builtin == bindingOf MStore = do
    let size = either (error . show) id $ sizeOf typeExpr
        nbOfWord256 = if size `mod` 32 == 0 then size `div` 32 else (size `div` 32) + 1
    value <- compile valueExpr
    offset <- compile offsetExpr
    pure $ value <> ((\x -> offset <> [push $ (x + 1) * 32, push size, SUB, ADD, MSTORE]) =<< [0 .. nbOfWord256 - 1]) <> offset
-- Builtin env.mload
compile (App (App (Field (Var (V "env" _)) (FieldSelection _ builtin _)) typeExpr) offsetExpr)
  | builtin == bindingOf MLoad = do
    let size = either (error . show) id $ sizeOf typeExpr
        nbOfWord256 = if size `mod` 32 == 0 then size `div` 32 else (size `div` 32) + 1
    offset <- compile offsetExpr
    pure $ (\x -> offset <> [push $ x * 32, ADD, MLOAD]) =<< [0 .. nbOfWord256 - 1]
-- Builtin env.<trivialUnaryFunction>
compile (App (Field (Var (V "env" _)) (FieldSelection _ builtin _)) x)
  | M.member builtin builtinOpcodes = do
    p <- compile x
    pure $ p <> fromMaybe (error "member; qed;") (builtinOpcodes M.!? builtin)
compile (App x y) = do
  p <- compile y
  q <- compile x
  pure $ p <> q
compile (Field x (FieldSelection _ y _)) = do
  let ty@(Record fields) = either (error . show) id $ D.typeWith initialContext x
      (RecordField _ fieldTy _ _) = (M.!) (toMap fields) y
      offset = either (error . show) id (offsetOf y ty) `div` 32
      size = either (error . show) id (sizeOf ty) `div` 32
      stackMax = size
      fieldSize = either (error . show) id (sizeOf fieldTy) `div` 32
      fieldStackStart = size - offset - 1
      fieldStackEnd = fieldStackStart - fieldSize + 1
      delta = stackMax - fieldStackEnd - fieldSize
  liftIO $
    putStrLn $
      "Selecting " <> T.unpack y
        <> " of type "
        <> show (prettyExpr fieldTy)
        <> " at offset "
        <> show offset
        <> " in "
        <> show (prettyExpr ty)
  p <- compile x
  let storeTemp i = [push $ (fieldSize - i - 1) * 32] <> mload 0x40 <> [ADD, MSTORE]
  let restoreTemp i = [push $ i * 32] <> mload 0x40 <> [ADD, MLOAD]
  pure $
    p
      <> traceShowId (replicate (fromIntegral fieldStackEnd) POP)
      <> traceShowId (storeTemp =<< [0 .. fieldSize - 1])
      <> traceShowId (replicate (fromIntegral delta) POP)
      <> traceShowId (restoreTemp =<< [0 .. fieldSize - 1])
compile (RecordLit fields) = do
  mconcat . M.elems <$> traverse (compile . recordFieldValue) (toMap fields)
compile x = error $ "NOT YET SUPPORTED :'(: " <> show x

allocate :: Word256 -> [Opcode]
allocate x = [push $ x * 32] <> mload 0x40 <> [ADD, push 0x40, MSTORE]

deallocate :: Word256 -> [Opcode]
deallocate x = [push $ x * 32] <> mload 0x40 <> [SUB, push 0x40, MSTORE]

push :: Integral a => a -> Opcode
push = PUSH . fromIntegral

mload :: Word256 -> [Opcode]
mload offset = [PUSH offset, MLOAD]

mstore :: Word256 -> Word256 -> [Opcode]
mstore value offset = [PUSH value, PUSH offset, MSTORE]

mstore8 :: Word256 -> Word256 -> [Opcode]
mstore8 value offset = [PUSH value, PUSH offset, MSTORE]

sload :: Word256 -> [Opcode]
sload key = [PUSH key, SLOAD]

sstore :: Word256 -> Word256 -> [Opcode]
sstore key value = [PUSH value, PUSH key, SSTORE]
