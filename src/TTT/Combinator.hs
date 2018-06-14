{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}


module TTT.Combinator (
    Uniform(..), SomeUniform(..), uniform
  , IsJust(..), isJust
  , decideAll, decideAny
  , withSum
  , indexN
  , mapIx, sMapIx, MapIx
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude.List hiding  (Sum)
import           Data.Singletons.Prelude.Maybe hiding (IsJust)
import           Data.Singletons.TH
import           Data.Type.Combinator.Singletons
import           Data.Type.Index
import           Data.Type.Product
import           Data.Type.Sum
import           Type.Family.Nat

data Uniform :: k -> [k] -> Type where
    UZ :: Uniform a '[a]
    US :: Uniform a as -> Uniform a (a ': as)

data SomeUniform :: [k] -> Type where
    SU :: Sing a -> Uniform a as -> SomeUniform as

uniform
    :: forall k (as :: [k]). SDecide k
    => Sing as
    -> Decision (SomeUniform as)
uniform = \case
    SNil            -> Disproved $ \case
      SU _ u -> case u of {}
    sx `SCons` SNil -> Proved $ SU sx UZ
    sx `SCons` ss@(_ `SCons` _) -> case uniform ss of
      Proved (SU sy us) -> case sx %~ sy of
        Proved Refl -> Proved $ SU sx (US us)
        Disproved v -> Disproved undefined
      Disproved vs -> Disproved $ \case
        SU s (US u) -> vs $ SU s u

data IsJust :: Maybe k -> Type where
    IsJust :: IsJust ('Just a)

isJust :: Sing a -> Decision (IsJust a)
isJust = \case
    SNothing -> Disproved $ \case {}
    SJust _  -> Proved IsJust

decideAll
    :: forall f as. ()
    => (forall a. Sing a -> Decision (f a))
    -> Sing as
    -> Decision (Prod f as)
decideAll f = go
  where
    go  :: Sing bs -> Decision (Prod f bs)
    go  = \case
      SNil         -> Proved Ø
      s `SCons` ss -> case f s of
        Proved p    -> case go ss of
          Proved ps    -> Proved $ p :< ps
          Disproved vs -> Disproved $ \case
            _ :< ps -> vs ps
        Disproved v -> Disproved $ \case
            p :< _ -> v p

decideAny
    :: forall f as. ()
    => (forall a. Sing a -> Decision (f a))
    -> Sing as
    -> Decision (Sum f as)
decideAny f = go
  where
    go  :: Sing bs -> Decision (Sum f bs)
    go  = \case
      SNil         -> Disproved $ \case {}
      s `SCons` ss -> case f s of
        Proved p    -> Proved $ InL p
        Disproved v -> case go ss of
          Proved ps    -> Proved $ InR ps
          Disproved vs -> Disproved $ \case
            InL p  -> v  p
            InR ps -> vs ps

withSum
    :: forall f as r. ()
    => Sum f as
    -> (forall a. Index as a -> f a -> r)
    -> r
withSum = \case
    InL x  -> \f -> f IZ x
    InR xs -> \f -> withSum xs (f . IS)

indexN
    :: Index as a
    -> N
indexN = \case
    IZ   -> Z
    IS i -> S $ indexN i

$(singletons [d|
  mapIx :: N -> (a -> a) -> [a] -> [a]
  mapIx Z     f (x:xs) = f x : xs
  mapIx (S n) f (x:xs) = x   : mapIx n f xs
  |])
