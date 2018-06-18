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
import           Data.Singletons.Prelude.Functor
import           Data.Singletons.Prelude.Monad
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Nat
import           Data.Type.Sel
import           TTT.Core

-- data WinLineProof :: [Maybe Piece] -> Piece -> Type where
--     WLPO :: WinLineProof '[ 'Just p ] p
--     WLPS :: WinLineProof xs p
--          -> WinLineProof ('Just p ': xs) p

-- data IsJust :: Maybe k -> Type where
--     IsJust :: IsJust ('Just a)

-- type Victory b p l = (Index b l, WinLineProof l p)
-- genDefunSymbols [''Victory]

-- type NotCats b = Σ (N, N) (TyCon (Coord b 'Nothing))

-- type SomeVictory b = Σ (Piece, [Maybe Piece]) (UncurrySym1 (VictorySym1 b))

-- data BoardOverProof :: Board -> Maybe GameOver -> Type where
--     BOPVictory :: Σ [Maybe Piece] (VictorySym2 (Lines b) p)
--                -> BoardOverProof b ('Just ('GOWin p))
--     BOPCats    :: Refuted (NotCats b)
--                -> Refuted (SomeVictory (Lines b))
--                -> BoardOverProof b ('Just 'GOCats)
--     BOPInPlay  :: Refuted (SomeVictory (Lines b))
--                -> NotCats b
--                -> BoardOverProof b 'Nothing

-- winLineProof
--     :: Sing l
--     -> Decision (Σ Piece (TyCon (WinLineProof l)))
-- winLineProof = \case
--     SNil -> Disproved $ \case _ :&: w -> case w of {}
--     SNothing `SCons` _ -> Disproved $ \case _ :&: w -> case w of {}
--     SJust x  `SCons` xs -> case go x xs of
--         Proved w -> Proved $ x :&: w
--         Disproved v -> Disproved $ \case
--           _ :&: WLPO   -> v WLPO
--           _ :&: WLPS w -> v (WLPS w)
--   where
--     go :: Sing a -> Sing as -> Decision (WinLineProof ('Just a ': as) a)
--     go x = \case
--       SNil -> Proved WLPO
--       SNothing `SCons` _ -> Disproved $ \case
--         WLPS w -> case w of {}
--       SJust y `SCons` xs -> case x %~ y of
--         Proved Refl -> case go x xs of
--           Proved w -> Proved (WLPS w)
--           Disproved v -> Disproved $ \case
--             WLPS w -> v w
--         Disproved v -> Disproved $ \case
--           WLPS WLPO     -> v Refl
--           WLPS (WLPS _) -> v Refl

-- victoryProof
--     :: Sing as
--     -> Decision (SomeVictory as)
-- victoryProof = \case
--     SNil -> Disproved $ \case
--       STuple2{} :&: (s, _) -> case s of {}
--     x `SCons` xs -> case winLineProof x of
--       Proved (p :&: w) -> Proved $ STuple2 p x :&: (SZ :&: SelZ, w)
--       Disproved v -> case victoryProof xs of
--         Proved (STuple2 p y :&: (i, w)) -> Proved $ STuple2 p y :&: (IS i, w)
--         Disproved vs -> Disproved $ \case
--           STuple2 p y :&: (i, w) -> case i of
--             _    :&: SelZ   -> v $ p :&: w
--             SS n :&: SelS s -> vs $ STuple2 p y :&: (n :&: s, w)

-- notCatsProof :: Sing b -> Decision (NotCats b)
-- notCatsProof = \case
--     SNil -> Disproved $ \case
--       STuple2 _ _ :&: Coord i _ -> case i of {}
--     x `SCons` xs -> case go x of
--       Proved (j :&: j') -> Proved $ STuple2 SZ j :&: Coord SelZ j'
--       Disproved v -> case notCatsProof xs of
--         Proved (STuple2 i j :&: Coord i' j') ->
--           Proved $ STuple2 (SS i) j :&: Coord (SelS i') j'
--         Disproved vs -> Disproved $ \case
--           STuple2 SZ     j :&: Coord SelZ      j' -> v $ j :&: j'
--           STuple2 (SS i) j :&: Coord (SelS i') j' ->
--             vs $ STuple2 i j :&: Coord i' j'
--   where
--     go :: Sing l -> Decision (Index l 'Nothing)
--     go = \case
--       SNil -> Disproved $ \case
--         _ :&: s -> case s of {}
--       SNothing `SCons` _ -> Proved IZ
--       SJust _ `SCons` xs -> case go xs of
--         Proved i -> Proved (IS i)
--         Disproved v -> Disproved $ \case
--           (SS i :&: SelS s) -> v $ i :&: s

-- -- | We want this to typecheck, but it doesn't :(

-- -- boardOverProof
-- --     :: Sing b
-- --     -> BoardOverProof b (BoardOver b)
-- -- boardOverProof b = case victoryProof (sLines b) of
-- --     Proved (STuple2 p l :&: v) -> BOPVictory (l :&: v)

data Uniform :: [k] -> k -> Type where
    UZ :: Uniform '[a] a
    US :: ((a == b) ~ 'True)
       => Uniform as a
       -> Uniform (b ': as) b
    -- US :: Uniform as a
    --    -> Uniform (a ': as) a

data WinLineProof :: [Maybe Piece] -> Maybe Piece -> Type where
    WLP :: Uniform as ('Just p)
        -> WinLineProof as ('Just p)
    WLD :: Refuted (Σ Piece (TyCon (Uniform as) .@#@$$$ JustSym0))
        -> WinLineProof as 'Nothing

uniform
    :: SDecide k
    => Sing (as :: [k])
    -> Decision (Σ k (TyCon (Uniform as)))
uniform = \case
    SNil -> Disproved $ \case _ :&: u -> case u of {}
    x `SCons` SNil -> Proved $ x :&: UZ
    -- x `SCons` xs@(_ `SCons` _) -> case uniform xs of
    --   Proved (y :&: u) -> case x %~ y of
    --     Proved Refl -> Proved $ x :&: US u
    --     Disproved v -> Disproved $ \case
    --       z :&: US u' -> case y %~ z of
    --         Proved Refl -> v Refl
    --         Disproved v' -> undefined

win_line_proof :: Sing l -> WinLineProof l (WinLine l)
win_line_proof l = case uniform l of
    Proved (SNothing :&: u) -> case u of
      UZ -> WLD $ \case
        _ :&: u' -> case u' of {}
      -- US _ -> WLD $ \case
      --   _ :&: u' -> case u' of {}
    -- Proved (SJust p :&: u) -> case u of
    --   UZ   -> WLP UZ
    --   US u -> WLP (US u)
    -- SNil -> WLP
    -- SNothing `SCons` _ -> WLPN
    -- SJust x `SCons` xs -> go x xs

fromUniform
    :: Uniform as ('Just p)
    -> WinLine as :~: 'Just p
fromUniform = \case
    UZ -> Refl
    US UZ -> Refl
    -- US u -> case fromUniform u of
    --   Refl -> _
    -- x `SCons` y `SCons` SNil -> \case
    --   US UZ -> Refl
      -- case x %== y of
      --            STrue -> Refl
    -- UZ         -> Refl
    -- US (US UZ) -> Refl
    -- US u -> case fromUniform u of
    --   Refl -> Refl

-- fromUniform
--     :: Sing as
--     -> Uniform as ('Just p)
--     -> WinLine as :~: 'Just p
-- fromUniform = \case
--     _ `SCons` SNil -> \case
--       UZ -> Refl
--     x `SCons` y `SCons` SNil -> \case
--       US UZ -> Refl
--       -- case x %== y of
--       --            STrue -> Refl
--     -- UZ         -> Refl
--     -- US (US UZ) -> Refl
--     -- US u -> case fromUniform u of
--     --   Refl -> Refl

--     go :: Sing a -> Sing as -> Decision (WinLineProof ('Just a ': as) a)
--     go x = \case
--       SNil -> Proved WLPO
--       SNothing `SCons` _ -> Disproved $ \case
--         WLPS w -> case w of {}
--       SJust y `SCons` xs -> case x %~ y of
--         Proved Refl -> case go x xs of
--           Proved w -> Proved (WLPS w)
--           Disproved v -> Disproved $ \case
--             WLPS w -> v w
--         Disproved v -> Disproved $ \case
--           WLPS WLPO     -> v Refl
--           WLPS (WLPS _) -> v Refl

  -- -- TODO: can we verify these? (see manual-proofs branch)
  -- winLine :: [Maybe Piece] -> Maybe Piece
  -- winLine []           = Nothing
  -- winLine (Nothing:_ ) = Nothing
  -- winLine (Just x :xs) = x <$ guard (all (== Just x) xs)

