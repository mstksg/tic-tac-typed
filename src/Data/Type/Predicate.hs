{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Predicate (
    All(..), all
  , Any(..), any
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding (All, Any)
import           Data.Type.Sel
import           Prelude hiding                 (all, any)

data All :: (k ~> Type) -> [k] -> Type where
    All :: (forall a n. Sel n as a -> f @@ a) -> All f as

data Any :: (k ~> Type) -> [k] -> Type where
    Any :: Sel n as a -> f @@ a -> Any f as

all :: forall k (f :: k ~> Type) (as :: [k]). ()
    => (forall a. Sing a -> Decision (f @@ a))
    -> Sing as
    -> Decision (All f as)
all f = go
  where
    go :: Sing bs -> Decision (All f bs)
    go = \case
      SNil -> Proved $ All $ \case {}
      x `SCons` xs -> case f x of
        Proved p -> case go xs of
          Proved (All ps) -> Proved $ All $ \case
            SelZ   -> p
            SelS s -> ps s
          Disproved v -> Disproved $ \case
            All ps -> v (All (ps . SelS))
        Disproved v -> Disproved $ \case
          All ps -> v (ps SelZ)

any :: forall f as. ()
    => (forall a. Sing a -> Decision (f @@ a))
    -> Sing as
    -> Decision (Any f as)
any f = go
  where
    go :: Sing bs -> Decision (Any f bs)
    go = \case
      SNil -> Disproved $ \case
        Any s _ -> case s of {}
      x `SCons` xs -> case f x of
        Proved p    -> Proved $ Any SelZ p
        Disproved r -> case go xs of
          Proved (Any s p) -> Proved $ Any (SelS s) p
          Disproved rs -> Disproved $ \case
            Any SelZ     p -> r  p
            Any (SelS s) p -> rs (Any s p)

