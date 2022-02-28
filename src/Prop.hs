{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Prop where

import Text.ParserCombinators.ReadP 
    (ReadP, readP_to_S, (<++), munch, satisfy, skipSpaces, 
     chainl1, chainr1, string, char, between)
import Text.ParserCombinators.Parsec
    ((<|>), choice, eof, letter, parse, spaces, try)
import Data.Char (isLower, isAlphaNum)
import Data.Function (fix)
import Test.QuickCheck
import Control.Monad


type Atom = String

data Prop =  Var Atom | T | F
            | Neg Prop
            | Conj Prop Prop 
            | Disj Prop Prop 
            | Cond Prop Prop 
            | Iff Prop Prop
    deriving (Eq)

infix 4 `Conj`
infix 3 `Disj`
infix 2 `Cond`
infix 1 `Iff`

-- Show instance for Prop
instance Show Prop where
    show T = show "⊤"
    show F = show "⊥"
    show (Var str) = show str
    show (Neg f) = "¬" ++ show f
    show (Conj f1 f2) =
        "(" ++ show f1 ++ " " ++ "∧" ++ " " ++ show f2 ++ ")"
    show (Disj f1 f2) =
        "(" ++ show f1 ++ " " ++ "∨" ++ " " ++ show f2 ++ ")"
    show (Cond f1 f2) =
        "(" ++ show f1 ++ " " ++ "→" ++ " " ++ show f2 ++ ")"
    show (Iff f1 f2) = 
        "(" ++ show f1 ++ " " ++ "↔" ++ " " ++ show f2 ++ ")"

-- Read instance for Prop
means :: String -> a -> ReadP a
name `means` meaning = skipSpaces *> string name *> pure meaning

parseBool =  "T" `means` T <++ "F" `means` F

parseVar = skipSpaces *> (Var <$> ((:) <$> satisfy isLower <*> munch isAlphaNum))

parens :: ReadP a -> ReadP a
parens = between (skipSpaces *> char '(') (skipSpaces *> char ')')

prefix :: ReadP a -> ReadP (a -> a) -> ReadP a
prefix p op = fix $ (<++) p . (<*>) op

instance Read Prop where
    readsPrec _ = readP_to_S prec0 where
        prec0 = chainr1 prec1 ("<->" `means` Iff)
        prec1 = chainr1 prec2 ("->" `means` Cond)
        prec2 = chainl1 prec3 ("|" `means` Disj)
        prec3 = chainl1 prec4 ("&"  `means` Conj)
        prec4 = prefix  prec5 ("~" `means` Neg)
        prec5 = parseVar <++ parens prec0 <++ parseBool
        parseVar = skipSpaces
                    *> (Var <$> ((:) <$> satisfy isLower
                                    <*> munch isAlphaNum))
        parseBool = "T" `means` T <++ "F" `means` F
        

-- Convertation to NNF
removeImpls :: Prop -> Prop
removeImpls (Neg f) = Neg (removeImpls f)
removeImpls (f `Conj` g) = (removeImpls f) `Conj` (removeImpls g)
removeImpls (f `Disj` g) = (removeImpls f) `Disj` (removeImpls g)
removeImpls (f `Cond` g) = (Neg (removeImpls f)) `Disj` (removeImpls g)
removeImpls (f `Iff` g) = ((Neg f') `Disj` g') `Conj` ((Neg g') `Disj` f')
    where f' = removeImpls f
          g' = removeImpls g
removeImpls f = f

removeNegs :: Prop -> Prop
removeNegs (Neg (Neg f)) = removeNegs f
removeNegs (Neg (f `Conj` g)) = 
    (removeNegs (Neg f)) `Disj` (removeNegs (Neg g))
removeNegs (Neg (f `Disj` g)) = 
    (removeNegs (Neg f)) `Conj` (removeNegs (Neg g))
removeNegs (Neg (f `Cond` g)) =
     removeNegs (f `Conj` (Neg g))
removeNegs (Neg (f `Iff` g)) = 
    removeNegs ((f `Conj` (Neg g)) `Disj` (g `Conj` (Neg f)))
removeNegs (f `Conj` g) = (removeNegs f) `Conj` (removeNegs g)
removeNegs (f `Disj` g) = (removeNegs f) `Disj` (removeNegs g)
removeNegs f = f

prop2nnf :: Prop -> Prop
prop2nnf f = removeNegs (removeImpls f)

str2nnf :: String -> Prop
str2nnf s = prop2nnf (read s)

-- Convertation to DNF
applyAndDistr :: Prop -> Prop
applyAndDistr (f `Conj` (g `Disj` h)) = 
    (applyAndDistr (f `Conj` g)) `Disj` (applyAndDistr (f `Conj` h))
applyAndDistr ((f `Disj` g) `Conj` h) =
    (applyAndDistr (f `Conj` h)) `Disj` (applyAndDistr (g `Conj` h))
applyAndDistr f = f

traversednf :: Prop -> Prop
traversednf (f `Disj` g) = (traversednf f) `Disj` (traversednf g)
traversednf (f `Conj` g) = 
    applyAndDistr ((traversednf f) `Conj` (traversednf g))
traversednf f  = f

prop2dnf :: Prop -> Prop
prop2dnf f = traversednf (prop2nnf f)

str2dnf :: String -> Prop
str2dnf s = prop2dnf (read s)

-- Convertation to CNF
swapnnfOps :: Prop -> Prop
swapnnfOps (f `Conj` g) = (swapnnfOps f) `Disj` (swapnnfOps g)
swapnnfOps (f `Disj` g) = (swapnnfOps f) `Conj` (swapnnfOps g)
swapnnfOps (Neg f) = Neg (swapnnfOps f)
swapnnfOps f = f

prop2cnf :: Prop -> Prop
prop2cnf f = swapnnfOps (traversednf (swapnnfOps (prop2nnf f)))

str2cnf :: String -> Prop
str2cnf s = prop2cnf (read s)

-- Arbitrary instance for QuickCheck
newtype AtomName = AtomName { atomName :: String }

instance Arbitrary AtomName where
    arbitrary = genName

genName :: Gen AtomName
genName = sized genName'
genName' n = AtomName <$> replicateM (n + 1) (oneof $ return <$> alphabet)
alphabet = (take 26 $ iterate succ 'a')

instance Arbitrary Prop where
    arbitrary = genProp

genProp :: Gen Prop
genProp = sized genProp'
genProp' 0 = fmap Var (atomName <$> arbitrary)
genProp' n | n > 15 = genProp' (n `div` 2)
genProp' n | n > 0 =
          oneof [fmap Var (atomName <$> arbitrary),
                 fmap Neg subprop,
                 liftM2 Conj subprop subprop,
                 liftM2 Disj subprop subprop,
                 liftM2 Cond subprop subprop,
                 liftM2 Iff subprop subprop]
          where subprop = genProp' (n `div` 2)
