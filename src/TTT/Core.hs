{-# LANGUAGE EmptyCase             #-}
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
  , placeBoard, PlaceBoard, sPlaceBoard
  -- ** Predicates on data types
  , Found
  , Winner, Cats
  , BoardResult(..), GameOver
  -- * Represent game state and updates
  , GameState(..)
  , Update(..), Coord(..), InPlay, startInPlay
  , play
  -- ** Verify
  , Pick(..), pick
  -- * Defunctionalization Symbols
  , ResWinSym0, ResWinSym1, ResCatsSym0
  , BoardSym0
  , CompBoardSym0
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
import           Data.Type.Nat
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
  type CompBoard = ([] :.: []) (Maybe Piece)

  -- The empty (starting) board
  emptyBoard :: Board
  emptyBoard = [ [Nothing, Nothing, Nothing]
               , [Nothing, Nothing, Nothing]
               , [Nothing, Nothing, Nothing]
               ]

  -- Place a piece on a board at given coordinates
  placeBoard :: N -> N -> Piece -> Board -> Board
  placeBoard i j p = mapIx i (setIx j (Just p))
  |])

-- ********************************
--  Predicates
-- ********************************

-- | Witness that a piece has won a row
data Victory :: [Maybe Piece] -> Piece -> Type where
    Victory :: All [] (EqualTo ('Just p)) @@ as
            -> Victory ('Just p ': as) p

-- | Parameterized Predicate that a given line has a given victor
data LineWon :: ParamPred [Maybe Piece] Piece
type instance Apply (LineWon as) p = Victory as p

instance Decidable (Found LineWon) where
    decide = \case
      SNil -> Disproved $ \case
        _ :&: v -> case v of {}
      SNothing `SCons` _ -> Disproved $ \case
        _ :&: v -> case v of {}
      SJust (x@Sing :: Sing p) `SCons` xs -> case decide @(All [] (EqualTo ('Just p))) xs of
        Proved p    -> Proved $ x :&: Victory p
        Disproved r -> Disproved $ \case
          _ :&: Victory a -> r a

instance Auto (Not (Found LineWon)) ('Nothing ': as) where
    auto (_ :&: w) = case w of {}

-- | Predicate that a board is won by a given player
type Winner = (PPMap LinesSym0 (AnyMatch [] LineWon) :: ParamPred Board Piece)

-- | Predicate that all spots have been played (cats game).
--
-- @
-- 'Cats' :: 'Predicate' 'Board'
-- @
type Cats = (All ([] :.: []) (NotNull Maybe) :: Predicate CompBoard)

-- ********************************
--  Witnesses
-- ********************************

-- | Witness that a game is in a specific mode.
--
-- Generate using 'Taken' for 'Found BoardResultFOr'.
data BoardResult :: Board -> Result -> Type where
    GMVictory :: Winner b @@ p
              -> BoardResult b ('ResWin p)
    GMCats    :: Not (Found Winner) @@ b
              -> Cats @@ 'Comp b
              -> BoardResult b 'ResCats

data GameOver :: ParamPred Board Result
type instance Apply (GameOver b) o = BoardResult b o

instance Decidable (Found GameOver) where
    decide b = case search @Winner b of
        Proved (p :&: v) -> Proved $ SResWin p :&: GMVictory v
        Disproved r      -> case decide @Cats (SComp b) of
          Proved c     -> Proved $ SResCats :&: GMCats r c
          Disproved r' -> Disproved $ \case
            SResWin p :&: GMVictory v -> r $ p :&: v
            SResCats  :&: GMCats _ c  -> r' c

type InPlay = Not (Found GameOver)

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
    GSUpdate :: InPlay @@ b1
             -> Update ij p        b1 b2
             -> GameState p        b1
             -> GameState (AltP p)    b2

-- | The empty board is in-play.
startInPlay :: InPlay @@ EmptyBoard
startInPlay = \case
    SResWin p :&: GMVictory v -> noVictor (p :&: v)
    SResCats  :&: GMCats _ c  -> noCats   c
  where
    noVictor :: Not (Found Winner) @@ EmptyBoard
    noVictor = autoNot @_ @(Found Winner)  @EmptyBoard
    noCats   :: Not Cats @@ 'Comp EmptyBoard
    noCats   = autoNotAll @(NotNull Maybe) $ IZ :? IZ

-- | Type-safe "play".
play
    :: forall b i j row p. ()
    => InPlay @@ b
    -> Sel i b    row
    -> Sel j row 'Nothing
    -> Sing p
    -> GameState p b
    -> GameState (AltP p) (PlaceBoard i j p b)
play r i j p = GSUpdate r (Update (Coord i j) p)
