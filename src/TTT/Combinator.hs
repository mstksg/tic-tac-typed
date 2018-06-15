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
    Uniform(..), uniform
  , IsJust(..), isJust
  , decideAll, decideAny
  , withSum
  , mapIx, sMapIx, MapIx, MapIxSym0, MapIxSym1, MapIxSym2, MapIxSym3
  , setIx, sSetIx, SetIx, SetIxSym0, SetIxSym1, SetIxSym2, SetIxSym3
  , Sel(..), selSing
  , overSel, mapIx_proof
  , setSel, setIx_proof
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.TH
import           Data.Type.Combinator.Singletons
import           Data.Type.Index
import           Data.Type.Product
import           Data.Type.Sum
import           Type.Family.Nat

data Uniform :: [k] -> Type where
    UZ :: Uniform '[a]
    US :: Uniform (a ': as) -> Uniform (a ': a ': as)

uniform
    :: forall k (as :: [k]). SDecide k
    => Sing as
    -> Decision (Uniform as)
uniform = \case
    SNil         -> Disproved $ \case {}
    x `SCons` xs -> uniform' x xs

uniform' :: forall k (a :: k) as. SDecide k
    => Sing a
    -> Sing as
    -> Decision (Uniform (a ': as))
uniform' x = go
  where
    go :: Sing bs -> Decision (Uniform (a ': bs))
    go = \case
      SNil -> Proved UZ
      y `SCons` SNil -> case x %~ y of
        Proved Refl -> Proved (US UZ)
        Disproved v -> Disproved $ \case US _ -> v Refl
      y `SCons` ss@(_ `SCons` _) -> case x %~ y of
        Proved Refl -> case go ss of
          Proved u    -> Proved (US u)
          Disproved v -> Disproved $ \case US u -> v u
        Disproved v -> Disproved $ \case US _ -> v Refl

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

data Sel :: N -> [k] -> k -> Type where
    SelZ :: Sel 'Z (a ': as) a
    SelS :: Sel n as a -> Sel ('S n) (b ': as) a

selSing
    :: Sel n as a
    -> Sing n
selSing = \case
    SelZ   -> SZ
    SelS i -> SS $ selSing i

$(singletons [d|
  mapIx :: N -> (a -> a) -> [a] -> [a]
  mapIx Z     f (x:xs) = f x : xs
  mapIx (S n) f (x:xs) =   x : mapIx n f xs

  setIx :: N -> a -> [a] -> [a]
  setIx i x = mapIx i (const x)
  |])

overSel
    :: forall k n (as :: [k]) (a :: k) (f :: k ~> k). ()
    => Sel n as a
    -> Sing f
    -> Sing as
    -> Sing (MapIx n f as)
overSel = \case
    SelZ -> \(SLambda f) -> \case
      x `SCons` xs -> f x `SCons` xs
    SelS n -> \f -> \case
      x `SCons` xs -> x `SCons` overSel n f xs

mapIx_proof
    :: forall n as a f. ()
    => Sel n as a
    -> Sing as
    -> Sel n (MapIx n f as) (f @@ a)
mapIx_proof = \case
    SelZ -> \case
      _ `SCons` _  -> SelZ
    SelS n -> \case
      _ `SCons` xs -> SelS $ mapIx_proof @_ @_ @_ @f n xs

setSel
    :: forall k n (as :: [k]) (a :: k) (b :: k). ()
    => Sel n as a
    -> Sing b
    -> Sing as
    -> Sing (SetIx n b as)
setSel = \case
    SelZ -> \y -> \case
      _ `SCons` xs -> y `SCons` xs
    SelS n -> \y -> \case
      x `SCons` xs -> x `SCons` setSel n y xs

setIx_proof
    :: Sel n as a
    -> Sing as
    -> Sel n (SetIx n b as) b
setIx_proof = \case
    SelZ -> \case
      _ `SCons` _ -> SelZ
    SelS n -> \case
      _ `SCons` xs -> SelS $ setIx_proof n xs
