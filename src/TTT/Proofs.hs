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
    place_board_proof
  , full_line_proof_1
  , full_line_proof_1'
  , full_line_proof_2
  , full_line_proof_2'
  , full_line_proof_3
  , win_or_cats_proof
  , won_no_cats_proof
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Nat
import           Data.Type.Sel
import           TTT.Core


  -- -- particularly tricky to verify, because of (==) being prop eq, not dec
  -- -- eq.  can this be worked around?
  -- winLine :: [Maybe Piece] -> Maybe Piece
  -- winLine []           = Nothing
  -- winLine (Nothing:_ ) = Nothing
  -- winLine (Just x :xs) = x <$ guard (all (== Just x) xs)


-- type WinAt as p n = (Sel n as ('Just p))

data NotNull :: [k] -> Type where
    NotNull :: NotNull (a ': as)

data AllPred :: (k ~> Type) -> [k] -> Type where
    AP :: (forall a n. Sel n as a -> f @@ a)
       -> AllPred f as

type IsTrue f x = (f @@ x) :~: 'True
genDefunSymbols [''IsTrue]

all_proof
    :: forall k (as :: [k]) (f :: k ~> Bool). ()
    => Sing as
    -> Sing f
    -> AllPred (IsTrueSym1 f) as
    -> All f as :~: 'True
all_proof _ _ _ = undefined
-- all_proof = \case
--     SNil -> \_ _ -> Refl
--     x `SCons` xs -> \f (AP a) -> case f @@ x of
--       STrue  -> case all_proof xs f (AP (a . SelS)) of
--         Refl -> _
--       SFalse -> case a SelZ of {}
      
-- case f SelZ of
--       Refl -> case all_proof xs (AP ())

type EqualJustP p x = (x == 'Just p) :~: 'True
genDefunSymbols [''EqualJustP]

-- win_line_proof
--     :: Sing as
--     -> Sing p
--     -> (AllPred (EqualJustPSym1 p) as, NotNull as)
--     -> WinLine as :~: 'Just p
-- win_line_proof = \case
--     SNil -> \_ (_, nn)   -> case nn of {}
--     SNothing `SCons` _ -> \_ (AP f, _) -> case f SelZ of {}
--     SJust x `SCons` xs -> \p (AP f, _) ->
--       case (x %== p, x %~ p) of
--         (STrue, Disproved _) -> error "mismatch between == and ~"
--         (STrue, Proved Refl) -> case all_proof xs _ (AP (_ . f . SelS)) of
--           Refl -> Refl
-- -- all_proof
-- --     :: forall k (as :: [k]) (f :: k ~> Bool). ()
-- --     => Sing as
-- --     -> Sing f
-- --     -> AllPred (IsTrueSym1 f) as
-- --     -> All f as :~: 'True
-- -- all_proof _ _ _ = undefined
--         -- (STrue, Proved Refl)  -> case xs of
--         --   SNil -> Refl
--         --   _ `SCons` _ -> case win_line_proof xs x (AP (f . SelS), NotNull) of
--         --     Refl -> Refl
--             -- Disproved _ -> error "mismatch between == and ~"
--           -- _ `SCons` _ -> case win_line_proof xs (AP (f . SelS), NotNull) of
--             -- Refl -> Refl
--         (SFalse, _) -> case f SelZ of {}

        -- Proved Refl -> Refl
        -- Disproved
    -- SJust x `SCons` xs -> \(AP f, _) -> case f SelZ
  
    -- case f SelZ of
    --   Refl -> Refl

-- win_line_proof
--     :: Sing as
--     -> WinLine as a :~: 'Just p
--     -> Σ N (Sel n as ('Just p)



place_board_proof
    :: forall i j b p a. ()
    => Coord b a '(i, j)
    -> Sing b
    -> Coord (PlaceBoard i j p b) ('Just p) '(i, j)
place_board_proof (Coord i j) b = Coord i' j'
  where
    i' = mapIx_proof @i @b @_ @(SetIxSym2 j ('Just p)) i b
    j' = setIx_proof @j @_ @a @('Just p)               j (selIx i b)

type SelNothing as n = Sel n as 'Nothing
genDefunSymbols [''SelNothing]

-- | If there is a blank spot on the board, 'FullLine' must be 'False'.
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

-- | If 'FullLine' is 'False', then there must exist some blank spot on the
-- board.
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

-- | If all possible positions are 'Just', then 'FullLine' must be 'True'.
full_line_proof_2
    :: Sing as
    -> (forall n a. Sel n as a -> IsJust a)
    -> FullLine as :~: 'True
full_line_proof_2 = \case
    SNil -> const Refl
    SNothing `SCons` _ -> \w -> case w SelZ of {}
    SJust _ `SCons` xs -> \w -> case full_line_proof_2 xs (w . SelS) of
      Refl -> Refl

-- | If 'FullLine' is 'True', it must mean that all possible positions are
-- 'Just'.
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

-- | To wrap up 'full_line_proof_1' and 'full_line_proof_3', just a proof
-- that the tests (exists some blank spot vs. all spots are fulled) are
-- actually mutually exclusive.
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

-- | For a full board, a 3-in-a-row will take precedence over a cats
-- result.
win_or_cats_proof
    :: ( FindMaybe WinLineSym0 (Lines b) ~ 'Just p
       , All FullLineSym0 b ~ 'True
       )
    => BoardOver b :~: 'Just ('GOWin p)
win_or_cats_proof = Refl

-- | It is impossible for a winning line to exist if the result is cats
won_no_cats_proof
    :: (FindMaybe WinLineSym0 (Lines b) :~: 'Just p)
    -> (BoardOver b :~: 'Just 'GOCats)
    -> Void
won_no_cats_proof Refl = \case {}
