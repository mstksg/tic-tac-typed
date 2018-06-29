{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
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
  -- * Represent game state and updates
  , GameState(..), AnyVictory
  , Update(..), Coord(..), InPlay, startInPlay
  , play
  , GameMode(..), SomeGameMode, gameMode
  -- ** Verify
  , Pick(..), pick
  -- * Defunctionalization Symbols
  , GOWinSym0, GOWinSym1, GOCatsSym0
  , BoardSym0
  , AltPSym0, AltPSym1
  , LinesSym0, LinesSym1
  , EmptyBoardSym0
  , PlaceBoardSym0, PlaceBoardSym1, PlaceBoardSym2, PlaceBoardSym3, PlaceBoardSym4
  ) where

import           Data.Kind
import           Data.List hiding                    (lines)
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding      (All, Any)
import           Data.Singletons.Prelude.List hiding (All, Any)
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Nat
import           Data.Type.Predicate
import           Data.Type.Sel
import           Data.Type.Universe
import           Prelude hiding                      (lines)

$(singletons [d|
  data Piece = PX | PO
    deriving (Show, Eq)

  data GameOver = GOCats
                | GOWin Piece
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

  -- Place a piece on a board at given coordinates
  placeBoard :: N -> N -> Piece -> Board -> Board
  placeBoard i j p = mapIx i (setIx j (Just p))
  |])

data Victory :: Piece -> [Maybe Piece] -> Type where
    Victory :: All [] (TyPred ((:~:) ('Just p))) @@ as
            -> Victory p ('Just p ': as)

data AnyVictory b :: Piece ~> Type
type instance Apply (AnyVictory b) p = Any [] (TyCon (Victory p)) @@ (Lines b)

data IsPlayed :: Maybe Piece -> Type where
    IsPlayed :: IsPlayed ('Just p)

instance Decide (TyPred IsPlayed) where
    decide = \case
      SNothing -> Disproved $ \case {}
      SJust _  -> Proved IsPlayed

type AllFull = All [] (All [] (TyPred IsPlayed))

data GameMode :: Board -> Maybe GameOver -> Type where
    GMVictory :: AnyVictory b @@ p
              -> GameMode b ('Just ('GOWin p))
    GMCats    :: Refuted (Σ Piece (AnyVictory b))
              -> AllFull @@ b
              -> GameMode b ('Just 'GOCats)
    GMInPlay  :: Refuted (Σ Piece (AnyVictory b))
              -> Refuted (AllFull @@ b)
              -> GameMode b 'Nothing

type SomeGameMode b = Σ (Maybe GameOver) (TyCon (GameMode b))

data SomeVictory :: [Maybe Piece] ~> Type
type instance Apply SomeVictory as = Σ Piece (FlipSym2 (TyCon Victory) as)

instance Decide SomeVictory where
    decide = \case
      SNil -> Disproved $ \case
        _ :&: v -> case v of {}
      SNothing `SCons` _ -> Disproved $ \case
        _ :&: v -> case v of {}
      mx@(SJust x) `SCons` xs -> case decideAll (mx %~) xs of
        Proved p -> Proved $ x :&: Victory p
        Disproved r -> Disproved $ \case
          _ :&: Victory a -> r a

anyVictory
    :: forall (b :: [[Maybe Piece]]). ()
    => Sing b
    -> Decision (Σ Piece (AnyVictory b))
anyVictory b = case decide @(Any [] SomeVictory) (sLines b) of
    Proved (WitAny s (p :&: v)) -> Proved $ p :&: WitAny s v
    Disproved r -> Disproved $ \case
      p :&: WitAny s v -> r $ WitAny s (p :&: v)

gameMode :: forall b. Sing b -> SomeGameMode b
gameMode b = case anyVictory b of
    Proved (p :&: v) -> SJust (SGOWin p) :&: GMVictory v
    Disproved r -> case decide @(All [] (All [] (TyPred IsPlayed))) b of
      Proved (c :: AllFull @@ b) -> SJust SGOCats :&: GMCats r c
      Disproved r' -> SNothing :&: GMInPlay r r'

type InPlay b = GameMode b 'Nothing

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

-- | The empty board is in-play.
startInPlay :: InPlay EmptyBoard
startInPlay = GMInPlay noVictor noCats
  where
    noVictor :: Refuted (Σ Piece (AnyVictory EmptyBoard))
    noVictor (_ :&: WitAny s (Victory _)) = case s of                  -- data kinds trips up ghc
      IS (IS (IS (IS (IS (IS (IS (IS t))))))) -> case t of {}
    noCats :: Refuted (AllFull @@ EmptyBoard)
    noCats a = case runWitAll (runWitAll a IZ) IZ of {}

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
