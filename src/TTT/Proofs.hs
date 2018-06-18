{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module TTT.Proofs (
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Nat
import           Data.Type.Sel
import           TTT.Core

data WinLineProof :: [Maybe Piece] -> Piece -> Type where
    WLPO :: WinLineProof '[ 'Just p ] p
    WLPS :: WinLineProof xs p
         -> WinLineProof ('Just p ': xs) p

data IsJust :: Maybe k -> Type where
    IsJust :: IsJust ('Just a)

type Victory b p l = (Index b l, WinLineProof l p)
genDefunSymbols [''Victory]

type NotCats b = Σ (N, N) (TyCon (Coord b 'Nothing))

type SomeVictory b = Σ (Piece, [Maybe Piece]) (UncurrySym1 (VictorySym1 b))

data BoardOverProof :: Board -> Maybe GameOver -> Type where
    BOPVictory :: Σ [Maybe Piece] (VictorySym2 (Lines b) p)
               -> BoardOverProof b ('Just ('GOWin p))
    BOPCats    :: Refuted (NotCats b)
               -> Refuted (SomeVictory (Lines b))
               -> BoardOverProof b ('Just 'GOCats)
    BOPInPlay  :: Refuted (SomeVictory (Lines b))
               -> NotCats b
               -> BoardOverProof b 'Nothing

winLineProof
    :: Sing l
    -> Decision (Σ Piece (TyCon (WinLineProof l)))
winLineProof = \case
    SNil -> Disproved $ \case _ :&: w -> case w of {}
    SNothing `SCons` _ -> Disproved $ \case _ :&: w -> case w of {}
    SJust x  `SCons` xs -> case go x xs of
        Proved w -> Proved $ x :&: w
        Disproved v -> Disproved $ \case
          _ :&: WLPO   -> v WLPO
          _ :&: WLPS w -> v (WLPS w)
  where
    go :: Sing a -> Sing as -> Decision (WinLineProof ('Just a ': as) a)
    go x = \case
      SNil -> Proved WLPO
      SNothing `SCons` _ -> Disproved $ \case
        WLPS w -> case w of {}
      SJust y `SCons` xs -> case x %~ y of
        Proved Refl -> case go x xs of
          Proved w -> Proved (WLPS w)
          Disproved v -> Disproved $ \case
            WLPS w -> v w
        Disproved v -> Disproved $ \case
          WLPS WLPO     -> v Refl
          WLPS (WLPS _) -> v Refl

victoryProof
    :: Sing as
    -> Decision (SomeVictory as)
victoryProof = \case
    SNil -> Disproved $ \case
      STuple2{} :&: (s, _) -> case s of {}
    x `SCons` xs -> case winLineProof x of
      Proved (p :&: w) -> Proved $ STuple2 p x :&: (SZ :&: SelZ, w)
      Disproved v -> case victoryProof xs of
        Proved (STuple2 p y :&: (i, w)) -> Proved $ STuple2 p y :&: (IS i, w)
        Disproved vs -> Disproved $ \case
          STuple2 p y :&: (i, w) -> case i of
            _    :&: SelZ   -> v $ p :&: w
            SS n :&: SelS s -> vs $ STuple2 p y :&: (n :&: s, w)

notCatsProof :: Sing b -> Decision (NotCats b)
notCatsProof = \case
    SNil -> Disproved $ \case
      STuple2 _ _ :&: Coord i _ -> case i of {}
    x `SCons` xs -> case go x of
      Proved (j :&: j') -> Proved $ STuple2 SZ j :&: Coord SelZ j'
      Disproved v -> case notCatsProof xs of
        Proved (STuple2 i j :&: Coord i' j') ->
          Proved $ STuple2 (SS i) j :&: Coord (SelS i') j'
        Disproved vs -> Disproved $ \case
          STuple2 SZ     j :&: Coord SelZ      j' -> v $ j :&: j'
          STuple2 (SS i) j :&: Coord (SelS i') j' ->
            vs $ STuple2 i j :&: Coord i' j'
  where
    go :: Sing l -> Decision (Index l 'Nothing)
    go = \case
      SNil -> Disproved $ \case
        _ :&: s -> case s of {}
      SNothing `SCons` _ -> Proved IZ
      SJust _ `SCons` xs -> case go xs of
        Proved i -> Proved (IS i)
        Disproved v -> Disproved $ \case
          (SS i :&: SelS s) -> v $ i :&: s

-- | We want this to typecheck, but it doesn't :(

-- boardOverProof
--     :: Sing b
--     -> BoardOverProof b (BoardOver b)
-- boardOverProof b = case victoryProof (sLines b) of
--     Proved (STuple2 p l :&: v) -> BOPVictory (l :&: v)
