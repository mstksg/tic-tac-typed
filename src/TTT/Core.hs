{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
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

module TTT.Core (
    Piece(..), SPiece()
  , Mode(..), SMode
  , Sing(SPX, SPO, SMPlay, SMStop)
  , altP, AltP, sAltP
  , lines, Lines, sLines
  , emptyBoard, sEmptyBoard, EmptyBoard
  -- , Victory(..)
  -- , Full, BoardWon
  -- , GameState(..)
  -- -- , Pick(..), pick
  -- , play
  -- , PlaceBoard
  -- , placeSel
  ) where

import           Data.Dependent.Sum
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding       (Flip)
import           Data.Singletons.Prelude.List hiding  (Sum)
import           Data.Singletons.Prelude.Maybe hiding (IsJust)
import           Data.Singletons.TH
import           Data.Type.Combinator
import           Data.Type.Combinator.Singletons
import           Data.Type.Index
import           Data.Type.Product
import           Data.Type.Sum
import           Prelude hiding                       (lines)
import           TTT.Combinator
import           Type.Family.Nat

$(singletons [d|
  data Piece = PX | PO
    deriving (Show, Eq)

  altP :: Piece -> Piece
  altP PX = PO
  altP PO = PX

  data Mode  = MPlay Piece
             | MStop (Maybe Piece)

  lines :: [[a]] -> [[a]]
  lines [[x1,y1,z1], [x2,y2,z2], [x3,y3,z3]]
    = [ [x1,y1,z1], [x2,y2,z2], [x3,y3,z3]
      , [x1,x2,x3], [y1,y2,y3], [z1,z2,z3]
      , [x1,y2,z3], [x3,y2,z1]
      ]

  emptyBoard :: [[Maybe Piece]]
  emptyBoard = [ [Nothing, Nothing, Nothing]
               , [Nothing, Nothing, Nothing]
               , [Nothing, Nothing, Nothing]
               ]
  |])

-- data Victory :: [Maybe k] -> Type where
--     V :: Uniform ('Just a ': as) -> Victory ('Just a ': as)

data WinLine :: k -> [Maybe k] -> Type where
    WL :: Uniform ('Just a ': as) -> WinLine a ('Just a ': as)

data WinBoard :: [[Maybe k]] -> k -> Type where
    WB :: Sum (WinLine p) (Lines b) -> WinBoard b p

type Full         = Prod (Prod IsJust)
-- type BoardWon b p = Sum (WinLine p) (Lines b)

full
    :: Sing b
    -> Decision (Full b)
full = decideAll (decideAll isJust)

winLine
    :: forall k (as :: [Maybe k]). SDecide k
    => Sing as
    -> Decision2 (Flip WinLine as)
winLine ss = case uniform ss of
    Proved u -> case ss of
      SNil               -> Disproved2 $ \_ -> \case {}
      SNothing `SCons` _ -> Disproved2 $ \_ -> \case {}
      SJust s  `SCons` _ -> Proved2 s $ Flip (WL u)
    Disproved v -> Disproved2 $ \_ -> \case
      Flip (WL u) -> v u

-- winBoard
--     :: forall k (b :: [[Maybe k]]). SDecide k
--     => Sing b
--     -> Decision2 (WinBoard b)
-- winBoard b = case decideAny victory . sLines

-- data GameState :: Mode -> [[Maybe Piece]] -> Type where
--     GSVictory :: Sum (WinLine p) (Lines b)
--               -> GameState ('MStop ('Just p)) b
--     GSCats    :: Refuted2 (WinBoard b)
--               -> Full b
--               -> GameState ('MStop 'Nothing) b
--     GSInPlay  :: Refuted2 (WinBoard b)
--               -> Refuted (Full b)
--               -> GameState ('MPlay p) b

-- gameState
--     :: Sing b
--     -> (GameState ('MPlay p) b -> r)
--     -> (forall j. GameState ('MStop j) b -> r)
--     -> r
-- gameState b f g = case boardWon b of
--     -- Proved won -> withSum won $ \i (V v) ->
--     --   g $ GSVictory (injectSum i (W v))
--     Disproved2 notwon -> case full b of
--       Proved filled ->
--         g $ GSCats notwon filled
--       Disproved notfilled ->
--         f $ GSInPlay notwon notfilled

-- -- data Pick :: N -> N -> [[Maybe Piece]] -> Type where
-- --     PickValid  :: Sel i b row -> Sel j row 'Nothing  -> Pick i j b
-- --     PickPlayed :: Sel i b row -> Sel j row ('Just p) -> Pick i j b
-- --     PickOoBX   :: OutOfBounds i b -> Sing j          -> Pick i j b
-- --     PickOoBY   :: OutOfBounds

-- -- data Pick :: [[Maybe Piece]] -> Type where
-- --     PickValid  :: Index b row -> Index row 'Nothing  -> Pick b
-- --     PickPlayed :: Index b row -> Index row ('Just p) -> Pick b
-- --     PickOoBX   :: N           -> N -> Pick b
-- --     PickOoBY   :: Index b row -> N -> Pick b

-- -- pick
-- --     :: N
-- --     -> N
-- --     -> Sing b
-- --     -> Pick b
-- -- pick i j b = case nIndex i b of
-- --     Nothing           -> PickOoBX i j
-- --     Just (row :=> i') -> case nIndex j row of
-- --       Nothing -> PickOoBY i' j
-- --       Just (p :=> j') -> case p of
-- --         SNothing -> PickValid  i' j'
-- --         SJust _  -> PickPlayed i' j'

-- $(singletons [d|
--   placeBoard :: N -> N -> Piece -> [[Maybe Piece]] -> [[Maybe Piece]]
--   placeBoard Z     j p (x:xs) = setIx j (Just p) x : xs
--   placeBoard (S n) j p (x:xs) =                  x : placeBoard n j p xs
--   |])

-- placeSel
--     :: forall b i j p row. ()
--     => Sel i b    row
--     -> Sel j row 'Nothing
--     -> Sing p
--     -> Sing b
--     -> Sing (PlaceBoard i j p b)
-- placeSel = \case
--     SelZ -> \j p -> \case
--       r `SCons` rs -> setSel j (SJust p) r `SCons` rs
--     SelS i -> \j p -> \case
--       r `SCons` rs ->                    r `SCons` placeSel i j p rs

-- play
--     :: forall (b :: [[Maybe Piece]]) b' i j row p r. (b' ~ PlaceBoard i j p b)
--     => Sel i b    row
--     -> Sel j row 'Nothing
--     -> Sing p
--     -> Sing b
--     -> (          Sing b' -> GameState ('MPlay (AltP p)) b' -> r)
--     -> (forall s. Sing b' -> GameState ('MStop s       ) b' -> r)
--     -> r
-- play i j p b f g = gameState b' (f b') (g b')
--   where
--     b' = placeSel i j p b

-- -- play
-- --     :: forall (b :: [[Maybe Piece]]) row p r. ()
-- --     => Index b row
-- --     -> Index row 'Nothing
-- --     -> Sing p
-- --     -> Sing b
-- --     -> (forall b'  . Sing b' -> GameState ('MPlay (AltP p)) b' -> r)
-- --     -> (forall b' j. Sing b' -> GameState ('MStop j       ) b' -> r)
-- --     -> r
-- -- play i j (fromSing->p) b f g = withSomeSing (place i j p b) $ \b' ->
-- --     gameState b' (f b') (g b')

-- -- TODO: can Play return a b' with a known `(Index b' row, Index row ('Just p))`?
-- -- but do we need to?
