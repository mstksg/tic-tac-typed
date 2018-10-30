{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE BlockArguments       #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Sel (
    Sel(..), SelPred
  , InBounds, OutOfBounds
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding (Any, Not)
import           Data.Singletons.Sigma
import           Data.Type.Lens
import           Data.Type.Predicate
import           Data.Type.Predicate.Param
import           Data.Type.Universe

-- TODO: implement Sel in terms of Index?

-- | A @'Sel' n as a@ is an index into a list @as@ that the @n@th index is
-- @a@.
data Sel :: N -> [k] -> k -> Type where
    SelZ :: Sel 'Z (a ': as) a
    SelS :: Sel n as a -> Sel ('S n) (b ': as) a

data SelPred :: N -> ParamPred [k] k
type instance Apply (SelPred n as) a = Sel n as a

type InBounds n    = Found (SelPred n)
type OutOfBounds n = Not (InBounds n)
-- type OutOfBounds n (as :: [k]) = Refuted (Σ k (TyCon (Sel n as)))
-- type OutOfBounds n = Not (Found (TyCon1(as :: [k]) = Refuted (Σ k (TyCon (Sel n as)))

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
