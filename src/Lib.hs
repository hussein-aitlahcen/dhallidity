{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Avoid lambda using `infix`" #-}

module Lib (execute) where

import Data.Bits (Bits (..))
import Data.Foldable (foldl', traverse_)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Void (Void)
import Data.Word (Word64)
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
import Dhall.Map (fromList)
import Dhall.Parser (exprFromText)
import Dhall.TypeCheck (typeWith)
import EVM.Opcode (Opcode (..), Opcode' (..), toHex)
import Numeric.Natural (Natural)

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
          "\
          \ let generate = https://prelude.dhall-lang.org/List/generate in\
          \ let c = List/fold Natural (generate 1000 Natural (\\(i : Natural) -> i)) Natural (\\(x: Natural) -> \\(y: Natural) -> x + y) 0 in\
          \ env.balanceOf env.address + c + env.selfBalance"
      )
  traverse_
    ( ( \validProgram ->
          traverse_
            (\programType -> go programType validProgram)
            (typeWith initialContext validProgram)
      )
        . denote
    )
    program
  where
    go :: Expr Void Void -> Expr Void Void -> IO ()
    go programType validProgram = do
      putStrLn ""
      putStrLn "== TYPE =="
      print programType
      putStrLn ""
      putStrLn "== BASE =="
      print (denote @_ @_ @Void validProgram)
      putStrLn ""
      putStrLn "== NORMALIZED =="
      let normalized :: Expr Void Void
          normalized = normalize validProgram
      print normalized
      putStrLn ""
      putStrLn "== ABSTRACT BYTECODES =="
      let compiled = compile normalized <> [STOP]
      print compiled
      putStrLn ""
      putStrLn "== HEX BYTECODES =="
      putStrLn $ toHex compiled

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
maxWord256 = maxWord128 `shiftL` 128 .|. maxWord128
  where
    maxWord64 = fromIntegral (maxBound @Word64)
    maxWord128 = maxWord64 `shiftL` 64 .|. maxWord64

compile :: Expr Void Void -> [Opcode]
compile (NaturalLit x)
  | x <= maxWord256 = [PUSH $ fromIntegral x]
compile (IntegerLit x)
  | x <= fromIntegral maxWord256 = [PUSH $ fromIntegral x]
compile (NaturalPlus x y) = compile x <> compile y <> [ADD]
compile (App (App NaturalSubtract x) y) = compile x <> compile y <> [SUB]
compile (Field (Var (V "env" _)) (FieldSelection _ builtin _))
  | M.member builtin builtinOpcodes =
    fromMaybe (error "member; qed;") $ builtinOpcodes M.!? builtin
compile (App (Field (Var (V "env" _)) (FieldSelection _ builtin _)) x)
  | M.member builtin builtinOpcodes =
    compile x <> fromMaybe (error "member; qed;") (builtinOpcodes M.!? builtin)
compile x = error $ "NOT YET SUPPORTED :'(: " <> show x
