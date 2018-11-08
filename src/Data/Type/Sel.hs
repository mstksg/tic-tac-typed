{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Type.Sel (
    Sel(..)
  , InBounds, OutOfBounds
  , Coord(..)
  -- , ixSel
  -- , sameSel
  , Placer(..)
  , Placed(..)
  , Place2D(..)
  -- , placer
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding (Any, Not)
import           Data.Singletons.Sigma
import           Data.Type.Lens
import           Data.Type.Predicate
import           Data.Type.Predicate.Param

-- TODO: implement Sel in terms of Index?

-- | A @'Sel' n as a@ is an index into a list @as@ that the @n@th index is
-- @a@.
data Sel :: N -> [k] -> k -> Type where
    SelZ :: Sel 'Z (a ': as) a
    SelS :: Sel n as a -> Sel ('S n) (b ': as) a

type InBounds n    = Found (TyPP (Sel n))
type OutOfBounds n = Not (InBounds n)


instance SingI n => Decidable (InBounds n) where
    decide = go sing
      where
        go :: Sing m -> Decide (InBounds m)
        go = \case
          SZ   -> \case
            SNil -> Disproved \case
              _ :&: s -> case s of {}
            x `SCons` _  -> Proved $ x :&: SelZ
          SS n -> \case
            SNil -> Disproved \case
              _ :&: s -> case s of {}
            _ `SCons` xs -> case go n xs of
              Proved (y :&: s) -> Proved $ y :&: SelS s
              Disproved v      -> Disproved \case
                y :&: s -> case s of
                  SelS m -> v (y :&: m)

-- | Represents a 2-d 'Sel'.
data Coord :: (N, N) -> [[k]] -> k -> Type where
    (:$:) :: Sel i xss xs
          -> Sel j xs  x
          -> Coord '(i, j) xss x

data Placer :: N -> k -> k -> [k] -> [k] -> Type where
    PlacerZ :: Placer 'Z     x y (x ': as) (y ': as)
    PlacerS :: Placer     n  x y       as        bs
            -> Placer ('S n) x y (a ': as) (a ': bs)

data Placed :: N -> k -> [k] -> Type where
    Placed :: Sing x
           -> Sing ys
           -> Placer n x y xs ys
           -> Placed n y xs

instance (SingI n, SingI x) => Decidable (TyPred (Placed n x)) where
    decide = placer sing sing

placer
    :: Sing (n :: N)
    -> Sing (x :: k)
    -> Sing (xs :: [k])
    -> Decision (Placed n x xs)
placer = \case
    SZ -> \x -> \case
      SNil         -> Disproved $ \(Placed _ _ p) -> case p of {}
      y `SCons` ys -> Proved    $ Placed y (x `SCons` ys) PlacerZ
    SS n -> \x -> \case
      SNil         -> Disproved $ \(Placed _ _ p) -> case p of {}
      y `SCons` ys -> case placer n x ys of
        Proved (Placed z ys' p) -> Proved $ Placed z (y `SCons` ys') (PlacerS p)
        Disproved v -> Disproved $ \(Placed z (_ `SCons` ys') (PlacerS p)) ->
          v $ Placed z ys' p

data Place2D :: (N, N) -> k -> k -> [[k]] -> [[k]] -> Type where
    P2D :: Placer i xs ys xss yss
        -> Placer j x  y  xs  ys
        -> Place2D '(i, j) x y xss yss


