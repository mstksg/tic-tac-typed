{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module TTT.Core (
  -- * Data Types
    Piece(..), SPiece
  , Result(..), SResult
  , Board
  , Sing(SPX, SPO, SResWin, SResCats)
  -- ** Functions on data types
  , altP, AltP, sAltP
  , lines, Lines, sLines
  , emptyBoard, EmptyBoard, sEmptyBoard
  , PlaceBoard, sPlaceBoard
  -- ** Predicates on data types
  , Found
  , Winner, Cats
  , GameOverWit(..), GameOver
  -- * Represent game state and updates
  , GameState(..)
  , Update(..), Coord(..), InPlay, startInPlay
  , play
  -- ** Verify
  , Pick(..)
  -- , pick
  -- * Defunctionalization Symbols
  , ResWinSym0, ResWinSym1, ResCatsSym0
  , BoardSym0
  , AltPSym0, AltPSym1
  , LinesSym0, LinesSym1
  , EmptyBoardSym0
  , PlaceBoardSym0, PlaceBoardSym1, PlaceBoardSym2, PlaceBoardSym3, PlaceBoardSym4
  ) where

import           Data.Kind
import           Data.List hiding                    (lines)
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding      (All, Any, Not, Null)
import           Data.Singletons.Prelude.List hiding (All, Any, Null)
import           Data.Singletons.Sigma
import           Data.Singletons.TH hiding           (Null)
import           Data.Type.Lens
import           Data.Type.Predicate
import           Data.Type.Predicate.Auto
import           Data.Type.Predicate.Param
import           Data.Type.Predicate.Quantification
import           Data.Type.Sel
import           Data.Type.Universe
import           Prelude hiding                      (lines)

-- ********************************
--  Types and type-level functions
-- ********************************

$(singletons [d|
  data Piece = PX | PO
    deriving (Show, Eq)

  data Result = ResCats
              | ResWin Piece
    deriving (Show, Eq)

  -- Alternate the piece; used to pick "next player"
  altP :: Piece -> Piece
  altP PX = PO
  altP PO = PX

  diagonal :: [[a]] -> [a]
  diagonal []          = []
  diagonal ((x:_):xss) = x : diagonal (map (drop 1) xss)

  -- Get all winnable three-in-a-row lines from a board
  lines :: [[a]] -> [[a]]
  lines xs = concat [ xs
                    , transpose xs
                    , [diagonal xs, diagonal (reverse xs)]
                    ]

  -- Representation of a board
  type Board = [[Maybe Piece]]

  -- The empty (starting) board
  emptyBoard :: Board
  emptyBoard = [ [Nothing, Nothing, Nothing]
               , [Nothing, Nothing, Nothing]
               , [Nothing, Nothing, Nothing]
               ]

  |])

$(singletonsOnly [d|
  placeBoard :: N -> N -> Piece -> Board -> Board
  placeBoard i j p = set (ixList i . ixList j) (Just p)
  |])

-- ********************************
--  Predicates
-- ********************************

-- | Witness that a row is won by a given piece.
data VicWit :: [Maybe Piece] -> Piece -> Type where
    VicWit :: All [] (EqualTo ('Just p)) @@ as
            -> VicWit ('Just p ': as) p

-- | Parameterized predicate that a piece has won a given row
--
-- @
-- 'Victory' :: 'ParamPred' [Maybe 'Piece'] Piece
-- @
type Victory = TyPP VicWit

instance Decidable (Found Victory) where
    decide = \case
      SNil -> Disproved \case
        _ :&: v -> case v of {}
      SNothing `SCons` _ -> Disproved \case
        _ :&: v -> case v of {}
      SJust (x@Sing :: Sing p) `SCons` xs -> case decide @(All [] (EqualTo ('Just p))) xs of
        Proved p    -> Proved $ x :&: VicWit p
        Disproved r -> Disproved \case
          _ :&: VicWit a -> r a

instance Auto (Not (Found Victory)) ('Nothing ': as) where
    auto (_ :&: w) = case w of {}

-- | Predicate that a board is won by a given player
--
-- @
-- Winner :: ParamPred Board Piece
-- @
type Winner = LinesSym0 `PPMap` AnyMatch [] Victory

-- | Predicate that all spots have been played (cats game).
--
-- @
-- 'Cats' :: 'Predicate' 'Board'
-- @
type Cats = All [] (All [] IsJust)

-- ********************************
--  Witnesses
-- ********************************

-- | Witness that a game is in a specific mode.
data GameOverWit :: Board -> Result -> Type where
    GOVictory :: Winner b @@ p
              -> GameOverWit b ('ResWin p)
    GOCats    :: Not (Found Winner) @@ b
              -> Cats @@ b
              -> GameOverWit b 'ResCats

-- | Parameterized predicate that a game is won by a player (or cats) for
-- for a given board.
--
-- @
-- GameOver :: ParamPred Board Result
-- @
type GameOver = TyPP GameOverWit

instance Decidable (Found GameOver) where
    decide b = case search @Winner b of
      Proved (p :&: v) -> Proved $ SResWin p :&: GOVictory v
      Disproved r      -> case decide @Cats b of
        Proved c     -> Proved $ SResCats :&: GOCats r c
        Disproved r' -> Disproved \case
          SResWin p :&: GOVictory v -> r $ p :&: v
          SResCats  :&: GOCats _ c  -> r' c

-- | A predicate that a game is still in play
type InPlay = Not (Found GameOver)

-- | Represents a legal update to a board (in-bounds, and does not
-- overwrite a played piece)
data Update :: Piece -> Board -> Board -> Type where
    Update :: forall i j p b b'. ()
           => Place2D '(i, j) 'Nothing ('Just p) b b'
           -> Update p b b'

-- | Potential results of 'pick': A verified move, or one of many failures
-- (with proof of failures)
data Pick :: (N, N, Board) -> Type where
    PickValid  :: Place2D '(i, j) 'Nothing  ('Just p) b b'    -> Pick '(i, j, b)
    PickPlayed :: Place2D '(i, j) ('Just p) p'        b b'    -> Sing p        -> Pick '(i, j, b)
    PickOoBX   :: OutOfBounds i @@ b                         -> Pick '(i, j, b)
    PickOoBY   :: Sel i b row        -> OutOfBounds j @@ row -> Pick '(i, j, b)

instance Provable (TyPred Pick) where
    prove (STuple3 (Sing :: Sing i) (Sing :: Sing j) b) =
      case searchTC b of
        Proved (row :&: i) -> case searchTC row of
          Proved (p :&: j) -> case p of
            SNothing -> PickValid (i :$: j)
            SJust c  -> PickPlayed (i :$: j) c
          Disproved v -> PickOoBY i v
        Disproved v -> PickOoBX v

-- | Current board and currently expected player.
--
-- Can only be constructed by appending valid moves onto a known valid game
-- state.
data GameState :: Piece -> Board -> Type where
    GSStart  :: GameState 'PX EmptyBoard
    GSUpdate :: InPlay @@ b1
             -> Update    p        b1 b2
             -> GameState p        b1
             -> GameState (AltP p)    b2

-- | The empty board is in-play.
startInPlay :: InPlay @@ EmptyBoard
startInPlay = \case
    SResWin p :&: GOVictory v -> noVictor (p :&: v)
    SResCats  :&: GOCats _ c  -> noCats   c
  where
    noVictor :: Not (Found Winner) @@ EmptyBoard
    noVictor = autoNot @_ @(Found Winner)  @EmptyBoard
    noCats   :: Not Cats @@ EmptyBoard
    noCats   = mapRefuted allComp
                $ autoNotAll @IsJust $ IZ :? IZ

-- | Type-safe "play".
play
    :: forall b i j p. ()
    => InPlay @@ b
    -> Coord '(i, j) b 'Nothing
    -> GameState p b
    -> GameState (AltP p) (PlaceBoard i j p b)
play r c = GSUpdate r (Update c)
