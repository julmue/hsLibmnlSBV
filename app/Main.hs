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
main = putStrLn "hello world"

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
-- symbolic versions of concrete functions
-- http://hackage.haskell.org/package/sbv-7.12/docs/src/Documentation.SBV.Examples.Puzzles.U2Bridge.html#U2Member
-- -- | Crossing times for each member of the band
-- crossTime :: U2Member -> Time
-- crossTime Bono  = 1
-- crossTime Edge  = 2
-- crossTime Adam  = 5
-- crossTime Larry = 10
--
-- -- | The symbolic variant.. The duplication is unfortunate.
-- sCrossTime :: SU2Member -> STime
-- sCrossTime m =   ite (m .== bono) (literal (crossTime Bono))
--                $ ite (m .== edge) (literal (crossTime Edge))
--                $ ite (m .== adam) (literal (crossTime Adam))
--                                   (literal (crossTime Larry)) -- Must be Larry

-- -----------------------------------------------------------------------------
-- Expert System
-- -----------------------------------------------------------------------------
-- predicates
data Service =
    MachineLearning
  | Server
mkSymbolicEnumeration ''Service

-- | Shorthands for symbolic versions
[machineLearning, server] = map literal [MachineLearning, Server]

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

[aws, strato, stratoCloud ] = map literal [AWS, Strato, StratoCloud]

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

hasService :: Company -> Service -> Bool
hasService = has services


-- hasSService :: SBV Company -> [SBV Service]
-- hasSService c s = ite (m .== aws)  (fromBool (hasService AWS))
--             $ ite (m .== strato) (fromBool (hasService Strato))
--                                  (fromBool (hasService StratoCloud))

has :: (Eq a2, Eq a1) => [(a2, a1)] -> a2 -> a1 -> Bool
has rel a b = b `elem` bs
  where
   bs = getBs rel a

getServices :: Company -> [Service]
getServices = getBs services

services :: [(Company, Service)]
services = [
    (AWS, MachineLearning)
  , (AWS, Server)
  ]

sServices = map lift2 services

-- -----------------------------------------------------------------------------
-- what doesn't work: Lists

-- this doesn't work with list functions because of merging issues
-- -> the returning lists have to be structurally identical i.e. same length
-- getSServices :: SBV Company -> [SBV Service]
-- getSServices m = ite (m .== aws) (map literal (getServices AWS))
--                $ ite (m .== strato) (map literal (getServices Strato))
--                                     (map literal (getServices StratoCloud)) -- must be stratoCloud
-- "select" is a generalization of ite

-- getSBs :: (Mergeable a, Mergeable b, EqSymbolic a) => [(a, b)] -> a -> [b]
-- getSBs relation a = fmap snd . sFilter ((.==) a . fst) $ relation
--
-- -- data.sbv.list.bounded
-- sFilter :: (Mergeable a) => (a -> SBool) -> [a] -> [a]
-- sFilter f [] = []
-- sFilter f (x:xs) = ite (f x) (x : sFilter f xs) (sFilter f xs)
-- -----------------------------------------------------------------------------

lift2 :: (SymWord a, SymWord b) => (a, b) -> (SBV a, SBV b)
lift2 (a, b) = (literal a, literal b)

lift3 :: (SymWord a, SymWord b, SymWord c) => (a, b, c) -> (SBV a, SBV b, SBV c)
lift3 (a, b, c) = (literal a, literal b, literal c)

lift4 :: (SymWord a, SymWord b, SymWord c, SymWord d) => (a, b, c, d) -> (SBV a, SBV b, SBV c, SBV d)
lift4 (a, b, c, d) = (literal a, literal b, literal c, literal d)

-- -----------------------------------------------------------------------------

-- defined below
-- getClosure :: Eq a => [(a,a)] -> a -> [a]
-- getClosure relation a = go relation a []
--   where
--     go [] _ acc = nub acc
--     go ((a1, a2): rels) a acc
--       | a1 == a = getClosure relation a2 ++ go rels a (a2:acc)
--       | otherwise = go rels a acc

getBs :: (Eq a, Eq b) => [(a, b)] -> a -> [b]
getBs relation a = fmap snd . filter ((==) a . fst) $ relation

-- -----------------------------------------------------------------------------

cDataLocationWL :: [Country]
cDataLocationWL = [
    Germany
  , Spain
  ]

cspServiceML :: Symbolic ()
cspServiceML = do
  (service :: SBV Service) <- free_
  (company :: SBV Company) <- free_
  constrain $ service `is` MachineLearning
  constrain $ (company, service) `sElem` sServices

solveCspServiceML = allSat cspServiceML


-- -----------------------------------------------------------------------------
-- minimal example ::

data Person
  = Mary
  | Richard
  | Claudia
  | Christian
  | Stephen

mkSymbolicEnumeration ''Person

[mary, richard, claudia, christian, stephen] =
  map literal [Mary, Richard, Claudia, Christian, Stephen]

childOf :: [(Person, Person)]
childOf = [
    (Mary, Richard) ,
    (Richard, Christian),
    (Christian, Stephen)]

getAncestors :: Person -> [Person]
getAncestors p = go childOf p []
  where
    go [] _ acc = nub acc
    go ((p1, p2): rels) a acc
      | p1 == p = go rels p (p2:acc) ++ getAncestors p2
      | otherwise = go rels a acc

-- symbolic version of getAncestors
getSAncestors :: SBV Person -> [SBV Person]
getSAncestors p = ite (p .== mary) (map literal (getAncestors Mary))
                $ ite (p .== richard) (map literal (getAncestors Richard))
                $ ite (p .== claudia) (map literal (getAncestors Claudia))
                $ ite (p .== christian) (map literal (getAncestors Christian))
                                        (map literal (getAncestors Stephen))

cspAncestors :: IO AllSatResult
cspAncestors = allSat $ do
  (person :: SBV Person) <- free_
  constrain $ bnot $ stephen `sElem` (getSAncestors person)

-- hm ...
