{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module TTT.Proofs (
    full_line_proof_1
  , full_line_proof_1'
  , full_line_proof_2
  , full_line_proof_2'
  , full_line_proof_3
  , win_or_cats_proof
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.List
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Nat
import           Data.Type.Sel
import           TTT.Core

type SelNothing as n = Sel n as 'Nothing
genDefunSymbols [''SelNothing]

full_line_proof_1
    :: Sing as
    -> Σ N (SelNothingSym1 as)
    -> FullLine as :~: 'False
full_line_proof_1 = \case
    SNil -> \case _ :&: s -> case s of {}
    SNothing `SCons` _ -> const Refl
    SJust _  `SCons` xs -> \case
      SZ   :&: s      -> case s of {}
      SS n :&: SelS s -> case full_line_proof_1 xs (n :&: s) of
        Refl -> Refl

full_line_proof_1'
    :: Sing as
    -> FullLine as :~: 'False
    -> Σ N (SelNothingSym1 as)
full_line_proof_1' = \case
    SNil -> \case {}
    SNothing `SCons` _  -> \case
      Refl -> SZ :&: SelZ
    SJust _  `SCons` xs -> \case
      Refl -> case full_line_proof_1' xs Refl of
        n :&: s -> SS n :&: SelS s

data IsJust :: Maybe k -> Type where
    IsJust :: IsJust ('Just a)

full_line_proof_2
    :: Sing as
    -> (forall n a. Sel n as a -> IsJust a)
    -> FullLine as :~: 'True
full_line_proof_2 = \case
    SNil -> const Refl
    SNothing `SCons` _ -> \w -> case w SelZ of {}
    SJust _ `SCons` xs -> \w -> case full_line_proof_2 xs (w . SelS) of
      Refl -> Refl

full_line_proof_2'
    :: Sing as
    -> FullLine as :~: 'True
    -> Sel n as a
    -> IsJust a
full_line_proof_2' = \case
    SNil -> \case
      Refl -> \case {}
    SNothing `SCons` _ -> \case {}
    SJust _ `SCons` xs -> \case
      Refl -> \case
        SelZ   -> IsJust
        SelS s -> case full_line_proof_2' xs Refl s of
          IsJust -> IsJust

full_line_proof_3
    :: Sing as
    -> (forall n a. Sel n as a -> IsJust a)
    -> Σ N (SelNothingSym1 as)
    -> Void
full_line_proof_3 = \case
    SNil -> \_ -> \case
      _ :&: s -> case s of {}
    SNothing `SCons` _ -> \f -> \case
      _ :&: s -> case f s of {}
    SJust _ `SCons` xs -> \f -> \case
      SZ   :&: s      -> case s of {}
      SS n :&: SelS s -> full_line_proof_3 xs (f . SelS) (n :&: s)

-- | A quick verification that for a full board, a 3-in-a-row will take
-- precedence over a cats result.
win_or_cats_proof
    :: ( FindMaybe WinLineSym0 (Lines b) ~ 'Just p
       , All FullLineSym0 b ~ 'True
       )
    => BoardOver b :~: 'Just ('GOWin p)
win_or_cats_proof = Refl
