{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}

module Data.Type.Sel (
    Sel(..), selSing
  , mapIx, sMapIx, MapIx
  , setIx, sSetIx, SetIx
  , overSel
  , setSel
  , listSel
  , OutOfBounds
  -- * Proofs
  , mapIx_proof
  , setIx_proof
  -- * Index
  , Index, SelIndex
  , pattern IZ
  , pattern IS
  -- * Defunctionalization Symbols
  , MapIxSym0, MapIxSym1, MapIxSym2, MapIxSym3
  , SetIxSym0, SetIxSym1, SetIxSym2, SetIxSym3
  , IndexSym0, IndexSym1, IndexSym2
  , SelIndexSym0, SelIndexSym1, SelIndexSym2, SelIndexSym3
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding     (Any)
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Nat

-- | A @'Sel' n as a@ is an index into a list @as@ that the @n@th index is
-- @a@.
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

type OutOfBounds n (as :: [k]) = Refuted (Σ k (TyCon (Sel n as)))

listSel
    :: forall k n (as :: [k]). ()
    => Sing n
    -> Sing as
    -> Decision (Σ k (TyCon (Sel n as)))
listSel = \case
    SZ -> \case
      SNil -> Disproved $ \case
        _ :&: s -> case s of {}
      s `SCons` _ -> Proved $ s :&: SelZ
    SS n -> \case
      SNil -> Disproved $ \case
        _ :&: s -> case s of {}
      _ `SCons` xs -> case listSel n xs of
        Proved (y :&: s) -> Proved (y :&: SelS s)
        Disproved v -> Disproved $ \case
          y :&: s -> case s of
            SelS m -> v (y :&: m)

type SelIndex as a n = Sel n as a
genDefunSymbols [''SelIndex]

type Index as a = Σ N (SelIndexSym2 as a)
genDefunSymbols [''Index]

pattern IZ :: Index (a ': as) a
pattern IZ = SZ :&: SelZ

pattern IS :: Index as b -> Index (a ': as) b
pattern IS i <- ((\case SS n :&: SelS s -> n :&: s)-> i)
  where
    IS (n :&: s) = SS n :&: SelS s

{-# COMPLETE IZ, IS #-}
