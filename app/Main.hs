{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
-- {-# LANGUAGE FlexibleContexts #-}

module Main where

import Data.SBV
-- import Data.SBV.Tuple
import qualified Data.SBV.List as SList
import qualified Data.SBV.List.Bounded as SList

import Control.Monad.Reader
import Data.List
import Data.Functor.Identity
import Data.Bifunctor

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
-- meaning every constructor is a proposition
-- constructors of one type a mutually exclusive for one feature
-- example: FuelEngine xor ElectricEngine

-- do type constructors like products and sums work?

-- whats with a hybrid?
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

-- misc helpers
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
mkSymbolicEnumeration ''Service

data Company =
    Amazon
  | AWS
  | Strato
  | StratoCloud
  | XSystems
  | BestRun
  | InfoStar
  | MegaCorp
  | Springer
  | CloudStar
mkSymbolicEnumeration ''Company

data Country =
    USA
  | Russia
  | China
  | Germany
  | Sweden
  | Greece
  | Spain
mkSymbolicEnumeration ''Country

-- relationships are expressed with lists of tuples
-- this should be in its own type

-- predicates
-- getDomiciles :: Company -> [Country]
-- getDomiciles = getBs . fmap sbvPair $ domicile
--   where
--     domicile :: [(Company, Country)]
--     domicile = [
--       (AWS, Germany),
--       (Amazon, USA),
--       (Amazon, Russia)
--       ]

-- getDataLocations :: SBV Company -> [SBV Country]
-- getDataLocations = getBs . fmap sbvPair $ dataLocation
--   where
--     dataLocation :: [(Company, Country)]
--     dataLocation = [
--         (StratoCloud, Germany)
--       , (StratoCloud, Spain)
--       , (StratoCloud, USA)
--       , (AWS, China)
--       , (AWS, USA)
--       , (AWS, Germany)
--       ]

-- getOwners :: SBV Company -> [SBV Company]
-- getOwners = getClosure . fmap sbvPair $ ownership
--   where
--     ownership :: [(Company, Company)]
--     ownership = [
--         (AWS, Amazon)
--       , (BestRun, XSystems)
--       , (Springer, MegaCorp)
--       , (StratoCloud, Strato)
--       , (CloudStar, BestRun)
--       ]

service :: [(Company, Service)]
service = [
      (AWS, MachineLearning),
      (AWS, Server)
      ]

sServices :: [(SBV Company, SBV Service)]
sServices = fmap sbvPair service

sbvPair :: (SymWord a, SymWord b) => (a, b) -> (SBV a, SBV b)
sbvPair = bimap literal literal

-- maybe we can get a something like getServicesGen a :: a Company -> [a Company]
-- the use Identity and SBV as
-- wrapPair :: (forall a . a -> f a) -> (a , b) -> (f a, f b)
-- wrapPair f = bimap f f
--
-- genGetServices :: Eq (f Company, f Service) => (forall a . a -> f a) -> f Company -> [f Service]
-- genGetServices f a = getBs (fmap (wrapPair f) service) a
--   where
--     service :: [(Company, Service)]
--     service = [
--       (AWS, MachineLearning),
--       (AWS, Server)
--       ]

-- -----------------------------------------------------------------------------

getClosure :: Eq a => [(a,a)] -> a -> [a]
getClosure relation a = go relation a []
  where
    go [] _ acc = nub acc
    go ((a1, a2): rels) a acc
      | a1 == a = getClosure relation a2 ++ go rels a (a2:acc)
      | otherwise = go rels a acc

-- getBs :: (Eq a, Eq b) => [(a, b)] -> a -> [b]
-- getBs relation a = fmap snd . filter ((==) a . fst) $ relation

-- getSBs :: (Mergeable a, Mergeable b, EqSymbolic a) => [(a, b)] -> a -> [b]
-- getSBs relation a = fmap snd . sFilter ((.==) a . fst) $ relation
--
-- -- data.sbv.list.bounded
-- sFilter :: (Mergeable a) => (a -> SBool) -> [a] -> [a]
-- sFilter f [] = []
-- sFilter f (x:xs) = ite (f x) (x : sFilter f xs) (sFilter f xs)

-- -----------------------------------------------------------------------------

cDataLocationWL :: [Country]
cDataLocationWL = [
    Germany
  , Spain
  ]

cspServiceML = do
  (service :: SBV Service) <- free_
  (company :: SBV Company) <- free_
  constrain $ service `is` MachineLearning

  -- searching like this is necessary cause we have 1:n with fixed company
  -- does this work without wrapping the literal?
  constrain $ (company, (literal MachineLearning)) `sElem` sServices




solveCspServiceML = allSat cspServiceML
