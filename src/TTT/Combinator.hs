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
  , ixSing
  , indexN
  , mapIx, sMapIx, MapIx, MapIxSym0, MapIxSym1, MapIxSym2, MapIxSym3
  , setIx, sSetIx, SetIx, SetIxSym0, SetIxSym1, SetIxSym2, SetIxSym3
  , nIndex
  , Sel(..), selSing
  , overSel, overSelWit
  , setSel, setSelWit
  , OutOfBounds(..)
  ) where

import           Data.Dependent.Sum
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.List hiding  (Sum)
import           Data.Singletons.Prelude.Maybe hiding (IsJust)
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

-- uni = \case
--     x `SCons` SNil -> Proved UZ
--     x `SCons` (_ `SCons` _) -> case uni
    -- SNil -> Proved $ UZ


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

ixSing
    :: Index as a
    -> Sing as
    -> Sing a
ixSing = \case
   IZ -> \case
     s `SCons` _ -> s
   IS i -> \case
     _ `SCons` ss -> ixSing i ss

indexN
    :: Index as a
    -> N
indexN = \case
    IZ   -> Z
    IS i -> S $ indexN i

nIndex
    :: forall k (as :: [k]). ()
    => N
    -> Sing as
    -> Maybe (DSum Sing (Index as))
nIndex = \case
    Z -> \case
      SNil -> Nothing
      s `SCons` _ -> Just $ s :=> IZ
    S i -> \case
      SNil -> Nothing
      _ `SCons` ss -> case nIndex i ss of
        Just (s :=> j) -> Just (s :=> IS j)
        Nothing        -> Nothing

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

-- overSel
--     :: forall k n (as :: [k]) (a :: k) (f :: k ~> k). ()
--     => Sel n as a
--     -> Sing f
--     -> Sing as
--     -> Sing (MapIx n f as)
-- overSel = \case
--     SelZ -> \f -> \case
--       x `SCons` xs -> (f @@ x) `SCons` xs
--     SelS n -> \f -> \case
--       x `SCons` xs -> x `SCons` overSel n f xs

-- overSel
--     :: forall k n (as :: [k]) (a :: k) (f :: k ~> k). ()
--     => Sel n as a
--     -> Sing f
--     -> Sing as
--     -> Sel n (MapIx n f as) (f @@ a)
-- overSel = \case
--     SelZ -> \f -> \case
--       x `SCons` xs -> SelZ
--     SelS n -> \f -> \case
--       x `SCons` xs -> SelS (overSel n f xs)

overSelWit
    :: forall k n (as :: [k]) (a :: k) (f :: k ~> k). ()
    => Sel n as a
    -> Sing f
    -> Sing as
    -> (Sing (MapIx n f as), Sel n (MapIx n f as) (f @@ a))
overSelWit = \case
    SelZ -> \(SLambda f) -> \case
      x `SCons` xs -> (f x `SCons` xs, SelZ)
    SelS n -> \f -> \case
      x `SCons` xs -> case overSelWit n f xs of
        (xs', n') -> (x `SCons` xs', SelS n')


overSel
    :: forall k n (as :: [k]) (a :: k) (f :: k ~> k). ()
    => Sel n as a
    -> Sing f
    -> Sing as
    -> Sing (MapIx n f as)
overSel i f = fst . overSelWit i f

setSelWit
    :: forall k n (as :: [k]) (a :: k) (b :: k). ()
    => Sel n as a
    -> Sing b
    -> Sing as
    -> (Sing (SetIx n b as), Sel n (SetIx n b as) b)
setSelWit = \case
    SelZ -> \y -> \case
      x `SCons` xs -> (y `SCons` xs, SelZ)
    SelS n -> \y -> \case
      x `SCons` xs -> case setSelWit n y xs of
        (xs', n') -> (x `SCons` xs', SelS n')

setSel
    :: forall k n (as :: [k]) (a :: k) (b :: k). ()
    => Sel n as a
    -> Sing b
    -> Sing as
    -> Sing (SetIx n b as)
setSel i x = fst . setSelWit i x

data OutOfBounds :: N -> [k] -> Type where
    OoBZ :: OutOfBounds n '[]
    OoBS :: OutOfBounds n as -> OutOfBounds ('S n) (a ': as)
