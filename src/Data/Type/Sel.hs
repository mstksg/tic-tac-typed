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
    Sel(..)
  , listSel
  , OutOfBounds
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding     (Any)
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Nat

-- TODO: implement Sel in terms of Index?

-- | A @'Sel' n as a@ is an index into a list @as@ that the @n@th index is
-- @a@.
data Sel :: N -> [k] -> k -> Type where
    SelZ :: Sel 'Z (a ': as) a
    SelS :: Sel n as a -> Sel ('S n) (b ': as) a

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

-- type SomeSel as a n = Sel n as a
-- genDefunSymbols [''SomeSel]

-- type Index as a = Σ N (SomeSelSym2 as a)
-- genDefunSymbols [''Index]

-- pattern IZ :: Index (a ': as) a
-- pattern IZ = SZ :&: SelZ

-- pattern IS :: Index as b -> Index (a ': as) b
-- pattern IS ns <- ((\case SS n :&: SelS s -> n :&: s)->ns)
--   where
--     IS (n :&: s) = SS n :&: SelS s
