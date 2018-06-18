{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module TTT.Core (
  -- * Data Types
    Piece(..), SPiece
  , GameOver(..), SGameOver
  , Board
  , Sing(SPX, SPO, SGOWin, SGOCats)
  -- ** Functions on data types
  , altP, AltP, sAltP
  , lines, Lines, sLines
  , emptyBoard, EmptyBoard, sEmptyBoard
  , placeBoard, PlaceBoard, sPlaceBoard
  , boardOver, BoardOver, sBoardOver
  -- * Represent game state and updates
  , GameState(..), Update(..), Coord(..), InPlay(..)
  , play
  -- ** Verify
  , Pick(..), pick
  -- * Utility functions
  , fullLine, FullLine, sFullLine
  , findMaybe, FindMaybe, sFindMaybe
  , winLine, WinLine, sWinLine
  -- * Defunctionalization Symbols
  , BoardSym0
  , AltPSym0, AltPSym1
  , LinesSym0, LinesSym1
  , EmptyBoardSym0
  , PlaceBoardSym0, PlaceBoardSym1, PlaceBoardSym2, PlaceBoardSym3, PlaceBoardSym4
  , BoardOverSym0, BoardOverSym1
  , FullLineSym0, FullLineSym1
  , FindMaybeSym0, FindMaybeSym1, FindMaybeSym2
  , WinLineSym0, WinLineSym1
  ) where

import           Control.Monad
import           Data.Kind
import           Data.List hiding              (lines)
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.List
import           Data.Singletons.Prelude.Monad
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Nat
import           Data.Type.Sel
import           Prelude hiding                (lines)

$(singletons [d|
  data Piece = PX | PO
    deriving (Show, Eq)

  data GameOver = GOCats
                | GOWin Piece
    deriving (Show, Eq)

  altP :: Piece -> Piece
  altP PX = PO
  altP PO = PX

  diagonal :: [[a]] -> [a]
  diagonal []          = []
  diagonal ((x:_):xss) = x : diagonal (map (drop 1) xss)

  lines :: [[a]] -> [[a]]
  lines xs = concat [ xs
                    , transpose xs
                    , [diagonal xs, diagonal (reverse xs)]
                    ]

  type Board = [[Maybe Piece]]

  emptyBoard :: Board
  emptyBoard = [ [Nothing, Nothing, Nothing]
               , [Nothing, Nothing, Nothing]
               , [Nothing, Nothing, Nothing]
               ]

  -- mapIx and setIx are verified
  placeBoard :: N -> N -> Piece -> Board -> Board
  placeBoard i j p = mapIx i (setIx j (Just p))

  (<|>) :: Maybe a -> Maybe a -> Maybe a
  Just x  <|> _ = Just x
  Nothing <|> y = y

  findMaybe :: (a -> Maybe b) -> [a] -> Maybe b
  findMaybe _ []     = Nothing
  findMaybe f (x:xs) = f x <|> findMaybe f xs

  -- particularly tricky to verify, because of (==) being prop eq, not dec
  -- eq.  can this be worked around?
  winLine :: [Maybe Piece] -> Maybe Piece
  winLine []           = Nothing
  winLine (Nothing:_ ) = Nothing
  winLine (Just x :xs) = x <$ guard (all (== Just x) xs)

  -- tested in 'full_line_proof_1' and 'full_line_proof_2'
  fullLine :: [Maybe Piece] -> Bool
  fullLine []           = True
  fullLine (Nothing:_ ) = False
  fullLine (Just _ :xs) = fullLine xs

  -- simple property test in 'win_or_cats_proof'
  boardOver :: Board -> Maybe GameOver
  boardOver b = (GOWin  <$> findMaybe winLine (lines b))
            <|> (GOCats <$  guard (all fullLine b)     )
  |])

-- | Witness that a given board is in play
data InPlay :: Board -> Type where
    InPlay :: (BoardOver b ~ 'Nothing) => InPlay b

-- | Represents a board and coordinate with the current item at position on
-- the board.
data Coord :: Board -> Maybe Piece -> (N, N) -> Type where
    Coord :: Sel i b   row
          -> Sel j row p
          -> Coord b p '(i, j)

-- | Represents a legal update to a board (in-bounds, and does not
-- overwrite a played piece)
data Update :: (N, N) -> Piece -> Board -> Board -> Type where
    Update :: Coord b 'Nothing '(i, j)
           -> Sing p
           -> Update '(i, j) p b (PlaceBoard i j p b)

-- | Potential results of 'pick': A verified move, or one of many failures
-- (with proof of failures)
data Pick :: N -> N -> Board -> Type where
    PickValid  :: Sel i b row     -> Sel j row 'Nothing  -> Pick i j b
    PickPlayed :: Sel i b row     -> Sel j row ('Just p) -> Sing p -> Pick i j b
    PickOoBX   :: OutOfBounds i b ->                        Pick i j b
    PickOoBY   :: Sel i b row     -> OutOfBounds j row   -> Pick i j b

-- | Validate a pick from given coordinates on a board
pick
    :: Sing i
    -> Sing j
    -> Sing b
    -> Pick i j b
pick i j b = case listSel i b of
    Proved (row :&: i') -> case listSel j row of
      Proved (p :&: j') -> case p of
        SJust q  -> PickPlayed i' j' q
        SNothing -> PickValid i' j'
      Disproved v -> PickOoBY i' v
    Disproved v -> PickOoBX v

-- | Current board and currently expected player.
--
-- Can only be constructed by appending valid moves onto a known valid game
-- state.
data GameState :: Piece -> Board -> Type where
    GSStart  :: GameState 'PX EmptyBoard
    GSUpdate :: InPlay b1
             -> Update ij p        b1 b2
             -> GameState p        b1
             -> GameState (AltP p)    b2

-- | Type-safe "play".
play
    :: forall b i j row p. ()
    => InPlay b
    -> Sel i b    row
    -> Sel j row 'Nothing
    -> Sing p
    -> GameState p b
    -> GameState (AltP p) (PlaceBoard i j p b)
play r i j p = GSUpdate r (Update (Coord i j) p)
