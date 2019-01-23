{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Data.SBV
import Control.Monad.Reader
-- import Data.SBV.Core.Data


main :: IO ()
main = undefined

thm1 :: IO ThmResult
thm1 = prove . forAll ["x"] $ \ (x::SWord8) -> x * 2 .== x + x

thm2 :: IO ThmResult
thm2 = prove . forAll ["x"] $ \ (x::SWord8) -> x * 3 .== x + x

thm3 :: IO ThmResult
thm3 = prove . forSome ["x"] $ \ (x::SWord8) -> x * 3 .== x + x

thm3' :: IO SatResult
thm3' = sat . forSome ["x"] $ \ (x::SWord8) -> x * 3 .== x + x

thm4 :: IO SatResult
thm4 = sat . forSome ["x", "y"] $ \ (x::SInteger) y ->
    x^2 + y^2 .== 25 &&& 3 * x + 4 * y .== 0

thm = sat . forSome ["x"] $ \ (x::SBool) -> x


-- -----------------------------------------------------------------------------
-- boolean logic

sTrue = fromBool True :: SBool
sFalse = fromBool False :: SBool

-- Symbolic SBools != SBool
-- symbolic is the Monad already - this is something like pure

-- dependency formulation
dep1 :: SBool -> SBool -> SBool
dep1 = \useFuel hasTank -> useFuel ==> hasTank

dep2 :: SBool -> SBool -> SBool
dep2 = \useElectricity hasBattery -> useElectricity ==> hasBattery


csp = do
  fuel <- sBool "useFuel"
  elec <- sBool "useElectricity"
  tank <- sBool "hasTank"
  batt <- sBool "hasBattery"
  ecar <- sBool "isECar"
  constrain $ ecar .== true
  constrain $ dep1 fuel tank
  constrain $ dep2 elec batt

getCspModels = allSat csp

-- use reader monad to get variable bindings
-- Symbolic SBool's can be run with sat
result = sat dep1
resultAll = allSat dep1
-- imp1 = useElectricity ==> hasBattery


-- car components
-- should be exhaustive for sat problem

data Engine =
    FuelEngine
  | ElectricEngine

mkSymbolicEnumeration ''Engine

type SEngine = SBV Engine

data EnergySupply =
    FuelTank
  | Battery

mkSymbolicEnumeration ''EnergySupply

type SEnergySupply = SBV EnergySupply

configuration = do
    (engine :: SEngine) <- free_
    (energySupply :: SEnergySupply) <- free_
    constrain $ engine `is` FuelEngine
    constrain $ r1 engine energySupply
  where
    r1 = FuelEngine `implies` FuelTank

solution = allSat configuration

is :: (SymWord a) => SBV a -> a -> SBool
a `is` v = a .== literal v

implies :: (SymWord a1, SymWord a2) => a1 -> a2 -> SBV a1 -> SBV a2 -> SBool
implies c1 c2 sc1 sc2 = sc1 .== literal c1 ==> sc2 .== literal c2


-- -----------------------------------------------------------------------------
-- Expert System
-- -----------------------------------------------------------------------------
-- predicates
data Service =
    MachineLearning
  | Server
  deriving (Show, Read, Eq)

data Provider =
    AWS
  | StratoCloud
  | CloudStar
  deriving (Show, Read, Eq)

data Company =
    Amazon
  | Strato
  | MegaCorp
  | Springer
  deriving (Show, Read, Eq)

data Country =
    USA
  | Russia
  | China
  | Germany
  deriving (Show, Read, Eq)


-- predicates
isBased :: Company -> Country -> Bool
isBased = undefined

-- relationships are expressed with lists of tuples
ownership :: [(Company, Company)]
ownership = [
  (Springer, Strato),
  (Strato, MegaCorp)
  ]

owners :: Company -> [Company]
owners = closure ownership

closure :: [(a,a)] -> a -> [a]
closure = undefined
