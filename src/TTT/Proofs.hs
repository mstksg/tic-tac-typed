{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module TTT.Proofs (
) where

-- module TTT.Proofs (
--     place_board_proof
--   , IsJustP(..)
--   , win_line_proof_1
--   , win_line_proof_1'
--   , win_line_proof_2
--   , all_matching_proof_1
--   , all_matching_proof_1'
--   , all_matching_proof_2
--   , IsJust(..)
--   , full_line_proof_1
--   , full_line_proof_1'
--   , full_line_proof_2
--   , full_line_proof_2'
--   , full_line_proof_3
--   , win_or_cats_proof
--   , won_no_cats_proof
--   ) where

-- import           Data.Kind
-- import           Data.Singletons
-- import           Data.Singletons.Prelude
-- import           Data.Singletons.Sigma
-- import           Data.Singletons.TH
-- import           Data.Type.Nat
-- import           Data.Type.Sel
-- import           TTT.Core

-- type IsTrue f x = (f @@ x) :~: 'True
-- genDefunSymbols [''IsTrue]

-- place_board_proof
--     :: forall i j b p a. ()
--     => Coord b a '(i, j)
--     -> Sing b
--     -> Coord (PlaceBoard i j p b) ('Just p) '(i, j)
-- place_board_proof (Coord i j) b = Coord i' j'
--   where
--     i' = mapIx_proof @i @b @_ @(SetIxSym2 j ('Just p)) i b
--     j' = setIx_proof @j @_ @a @('Just p)               j (selIx i b)


-- data IsJustP :: Piece -> Maybe Piece -> Type where
--     IsJustP :: ((p == q) ~ 'True) => IsJustP p ('Just q)

-- data PropDec :: k -> k -> Type where
--     PDEq  :: ((a == b) ~ 'True, a ~ b)
--           => PropDec a b
--     PDNEq :: ((a == b) ~ 'False)
--           => Refuted (a :~: b)
--           -> PropDec a b

-- type SelNothing as n = Sel n as 'Nothing
-- genDefunSymbols [''SelNothing]

-- propDecPiece :: SPiece p -> SPiece q -> PropDec p q
-- propDecPiece = \case
--     SPX -> \case
--       SPX -> PDEq
--       SPO -> PDNEq $ \case {}
--     SPO -> \case
--       SPX -> PDNEq $ \case {}
--       SPO -> PDEq

-- win_line_proof_1
--     :: Sing (a ': as)
--     -> Sing p
--     -> (forall n b. Sel n (a ': as) b -> IsJustP p b)
--     -> WinLine (a ': as) :~: 'Just p
-- win_line_proof_1 = \case
--     SNothing `SCons` _ -> \_ f -> case f SelZ of {}
--     SJust x `SCons` xs -> \p f -> case propDecPiece p x of
--       PDEq -> case all_matching_proof_1 x xs (f . SelS) of
--         Refl -> Refl
--       PDNEq _ -> case f SelZ of {}

-- win_line_proof_1'
--     :: Sing (a ': as)
--     -> Sing p
--     -> (WinLine (a ': as) :~: 'Just p)
--     -> Sel n (a ': as) b
--     -> IsJustP p b
-- win_line_proof_1' = \case
--     SNothing `SCons` _  -> \_ -> \case {}
--     SJust _  `SCons` xs -> \y -> \case
--       Refl -> \case
--         SelZ -> undefined       -- !!
--         SelS s -> case all_matching_proof_1' y xs undefined s of     -- !!
--           IsJustP -> IsJustP

-- win_line_proof_2
--     :: Sing as
--     -> Σ N (SelNothingSym1 as)
--     -> WinLine as :~: 'Nothing
-- win_line_proof_2 = \case
--     SNil -> const Refl
--     SNothing `SCons` _ -> const Refl
--     SJust x `SCons` xs -> \case
--       SZ   :&: s      -> case s of {}
--       SS n :&: SelS s -> case all_matching_proof_2 x xs (n :&: s) of
--         Refl -> Refl

-- all_matching_proof_1
--     :: Sing p
--     -> Sing as
--     -> (forall n a. Sel n as a -> IsJustP p a)
--     -> AllMatching p as :~: 'Just p
-- all_matching_proof_1 x = \case
--     SNil -> const Refl
--     SNothing `SCons` _ -> \f -> case f SelZ of {}
--     SJust y `SCons` xs -> \f -> case propDecPiece x y of
--       PDEq -> case all_matching_proof_1 y xs (f . SelS) of
--         Refl -> Refl
--       PDNEq _ -> case f SelZ of {}

-- all_matching_proof_1'
--     :: forall p as n a. ()
--     => Sing p
--     -> Sing as
--     -> AllMatching p as :~: 'Just p
--     -> Sel n as a
--     -> IsJustP p a
-- all_matching_proof_1' x = \case
--     SNil -> \case
--       Refl -> \case {}
--     SNothing `SCons` _ -> \case {}
--     SJust y `SCons` xs -> case propDecPiece x y of
--       PDEq -> \case
--         Refl -> \case
--           SelZ -> IsJustP
--           SelS s -> case all_matching_proof_1' y xs undefined s of  -- !!
--             IsJustP -> IsJustP
--       PDNEq _ -> \case {}

-- all_matching_proof_2
--     :: Sing p
--     -> Sing as
--     -> Σ N (SelNothingSym1 as)
--     -> AllMatching p as :~: 'Nothing
-- all_matching_proof_2 x = \case
--     SNil -> \case 
--       _ :&: s -> case s of {}
--     SNothing `SCons` ys -> \case
--       SZ :&: SelZ -> Refl
--       SS n :&: SelS s -> case all_matching_proof_2 x ys (n :&: s) of
--         Refl -> Refl
--     SJust y `SCons` ys -> \case
--         SZ   :&: s      -> case s of {}
--         SS n :&: SelS s -> case propDecPiece x y of
--           PDEq    -> case all_matching_proof_2 y ys (n :&: s) of
--             Refl -> Refl
--           PDNEq _ -> case all_matching_proof_2 y ys (n :&: s) of
--             Refl -> Refl

-- -- | If there is a blank spot on the board, 'FullLine' must be 'False'.
-- full_line_proof_1
--     :: Sing as
--     -> Σ N (SelNothingSym1 as)
--     -> FullLine as :~: 'False
-- full_line_proof_1 = \case
--     SNil -> \case _ :&: s -> case s of {}
--     SNothing `SCons` _ -> const Refl
--     SJust _  `SCons` xs -> \case
--       SZ   :&: s      -> case s of {}
--       SS n :&: SelS s -> case full_line_proof_1 xs (n :&: s) of
--         Refl -> Refl

-- -- | If 'FullLine' is 'False', then there must exist some blank spot on the
-- -- board.
-- full_line_proof_1'
--     :: Sing as
--     -> FullLine as :~: 'False
--     -> Σ N (SelNothingSym1 as)
-- full_line_proof_1' = \case
--     SNil -> \case {}
--     SNothing `SCons` _  -> \case
--       Refl -> SZ :&: SelZ
--     SJust _  `SCons` xs -> \case
--       Refl -> case full_line_proof_1' xs Refl of
--         n :&: s -> SS n :&: SelS s

-- data IsJust :: Maybe k -> Type where
--     IsJust :: IsJust ('Just a)

-- -- | If all possible positions are 'Just', then 'FullLine' must be 'True'.
-- full_line_proof_2
--     :: Sing as
--     -> (forall n a. Sel n as a -> IsJust a)
--     -> FullLine as :~: 'True
-- full_line_proof_2 = \case
--     SNil -> const Refl
--     SNothing `SCons` _ -> \w -> case w SelZ of {}
--     SJust _ `SCons` xs -> \w -> case full_line_proof_2 xs (w . SelS) of
--       Refl -> Refl

-- -- | If 'FullLine' is 'True', it must mean that all possible positions are
-- -- 'Just'.
-- full_line_proof_2'
--     :: Sing as
--     -> FullLine as :~: 'True
--     -> Sel n as a
--     -> IsJust a
-- full_line_proof_2' = \case
--     SNil -> \case
--       Refl -> \case {}
--     SNothing `SCons` _ -> \case {}
--     SJust _ `SCons` xs -> \case
--       Refl -> \case
--         SelZ   -> IsJust
--         SelS s -> case full_line_proof_2' xs Refl s of
--           IsJust -> IsJust

-- -- | To wrap up 'full_line_proof_1' and 'full_line_proof_3', just a proof
-- -- that the tests (exists some blank spot vs. all spots are fulled) are
-- -- actually mutually exclusive.
-- full_line_proof_3
--     :: Sing as
--     -> (forall n a. Sel n as a -> IsJust a)
--     -> Σ N (SelNothingSym1 as)
--     -> Void
-- full_line_proof_3 = \case
--     SNil -> \_ -> \case
--       _ :&: s -> case s of {}
--     SNothing `SCons` _ -> \f -> \case
--       _ :&: s -> case f s of {}
--     SJust _ `SCons` xs -> \f -> \case
--       SZ   :&: s      -> case s of {}
--       SS n :&: SelS s -> full_line_proof_3 xs (f . SelS) (n :&: s)

-- -- TODO: Check the situation if more than one player wins

-- -- | For a full board, a 3-in-a-row will take precedence over a cats
-- -- result.
-- win_or_cats_proof
--     :: ( FindMaybe WinLineSym0 (Lines b) ~ 'Just p
--        , All FullLineSym0 b ~ 'True
--        )
--     => BoardOver b :~: 'Just ('GOWin p)
-- win_or_cats_proof = Refl

-- -- | It is impossible for a winning line to exist if the result is cats
-- won_no_cats_proof
--     :: (FindMaybe WinLineSym0 (Lines b) :~: 'Just p)
--     -> (BoardOver b :~: 'Just 'GOCats)
--     -> Void
-- won_no_cats_proof Refl = \case {}
