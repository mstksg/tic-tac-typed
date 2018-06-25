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
  , GameState(..), Update(..), Coord(..), InPlay, startInPlay
  , play
  , GameMode(..), SomeGameMode, gameMode
  -- ** Verify
  , Pick(..), pick
  -- * Utility functions
  -- * Defunctionalization Symbols
  , BoardSym0
  , AltPSym0, AltPSym1
  , LinesSym0, LinesSym1
  , EmptyBoardSym0
  , PlaceBoardSym0, PlaceBoardSym1, PlaceBoardSym2, PlaceBoardSym3, PlaceBoardSym4
  , GOWinSym0, GOWinSym1, GOCatsSym0
  ) where

import           Control.Monad
import           Data.Kind
import           Data.List hiding                    (lines, all, any)
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding      (All, Any)
import           Data.Singletons.Prelude.List hiding (All, Any)
import           Data.Singletons.Prelude.Monad hiding (Void)
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Nat
import           Data.Type.Sel
import           Prelude hiding                      (lines, all, any)

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

  -- proofs in "TTT.Proofs"
  placeBoard :: N -> N -> Piece -> Board -> Board
  placeBoard i j p = mapIx i (setIx j (Just p))
  |])

data All :: (k ~> Type) -> [k] -> Type where
    All :: (forall a n. Sel n as a -> f @@ a) -> All f as

data Any :: (k ~> Type) -> [k] -> Type where
    Any :: Sel n as a -> f @@ a -> Any f as

data Victory :: Piece -> [Maybe Piece] -> Type where
    Victory :: All (TyCon ((:~:) ('Just p))) as
            -> Victory p ('Just p ': as)

type AnyVictory b p = Any (TyCon (Victory p)) (Lines b)
genDefunSymbols [''AnyVictory]

data IsJust :: Maybe Piece -> Type where
    IsJust :: IsJust ('Just p)

isJust :: Sing a -> Decision (IsJust a)
isJust = \case
    SNothing -> Disproved $ \case {}
    SJust _  -> Proved IsJust

type AllFull b = All (TyCon1 (All (TyCon1 IsJust))) b

data GameMode :: Board -> Maybe GameOver -> Type where
    GMVictory :: AnyVictory b p
              -> GameMode b ('Just ('GOWin p))
    GMCats    :: Refuted (Σ Piece (AnyVictorySym1 b))
              -> AllFull b
              -> GameMode b ('Just 'GOCats)
    GMInPlay  :: Refuted (Σ Piece (AnyVictorySym1 b))
              -> Refuted (AllFull b)
              -> GameMode b 'Nothing

type SomeGameMode b = Σ (Maybe GameOver) (TyCon (GameMode b))

all :: forall k (f :: k ~> Type) (as :: [k]). ()
    => (forall a. Sing a -> Decision (f @@ a))
    -> Sing as
    -> Decision (All f as)
all f = go
  where
    go :: Sing bs -> Decision (All f bs)
    go = \case
      SNil -> Proved $ All $ \case {}
      x `SCons` xs -> case f x of
        Proved p -> case go xs of
          Proved (All ps) -> Proved $ All $ \case
            SelZ   -> p
            SelS s -> ps s
          Disproved v -> Disproved $ \case
            All ps -> v (All (ps . SelS))
        Disproved v -> Disproved $ \case
          All ps -> v (ps SelZ)

any :: forall f as. ()
    => (forall a. Sing a -> Decision (f @@ a))
    -> Sing as
    -> Decision (Any f as)
any f = go
  where
    go :: Sing bs -> Decision (Any f bs)
    go = \case
      SNil -> Disproved $ \case
        Any s _ -> case s of {}
      x `SCons` xs -> case f x of
        Proved p    -> Proved $ Any SelZ p
        Disproved r -> case go xs of
          Proved (Any s p) -> Proved $ Any (SelS s) p
          Disproved rs -> Disproved $ \case
            Any SelZ     p -> r  p
            Any (SelS s) p -> rs (Any s p)

type SomeVictory as = Σ Piece (FlipSym2 (TyCon Victory) as)
genDefunSymbols [''SomeVictory]

someVictory
    :: forall (as :: [Maybe Piece]). ()
    => Sing as
    -> Decision (SomeVictory as)
someVictory = \case
    SNil -> Disproved $ \case
      _ :&: v -> case v of {}
    SNothing `SCons` _ -> Disproved $ \case
      _ :&: v -> case v of {}
    mx@(SJust x) `SCons` xs -> case all (mx %~) xs of
      Proved p -> Proved $ x :&: Victory p
      Disproved r -> Disproved $ \case
        _ :&: Victory (All f) -> r (All f)
  
anyVictory
    :: forall (b :: [[Maybe Piece]]). ()
    => Sing b
    -> Decision (Σ Piece (AnyVictorySym1 b))
anyVictory b = case any @SomeVictorySym0 someVictory (sLines b) of
    Proved (Any s (p :&: v)) -> Proved $ p :&: Any s v
    Disproved r -> Disproved $ \case
      p :&: Any s v -> r $ Any s (p :&: v)

gameMode :: forall b. Sing b -> SomeGameMode b
gameMode b = case anyVictory b of
    Proved (p :&: v) -> SJust (SGOWin p) :&: GMVictory v
    Disproved r -> case all (all @_ @(TyCon1 IsJust) isJust) b of
      Proved (c :: AllFull b) -> SJust SGOCats :&: GMCats r c
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

startInPlay :: InPlay EmptyBoard
startInPlay = GMInPlay noVictor noCats
  where
    noVictor :: Refuted (Σ Piece (AnyVictorySym1 EmptyBoard))
    noVictor (_ :&: Any s (Victory _)) = case s of
      SelS (SelS (SelS (SelS (SelS (SelS (SelS (SelS t))))))) -> case t of {}
    noCats :: Refuted (AllFull EmptyBoard)
    noCats (All f) = case f SelZ of
                       All g -> case g SelZ of
                         {}

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
