{-# LANGUAGE AllowAmbiguousTypes             #-}
{-# LANGUAGE DataKinds                       #-}
{-# LANGUAGE EmptyCase                       #-}
{-# LANGUAGE FlexibleInstances               #-}
{-# LANGUAGE GADTs                           #-}
{-# LANGUAGE InstanceSigs                    #-}
{-# LANGUAGE KindSignatures                  #-}
{-# LANGUAGE LambdaCase                      #-}
{-# LANGUAGE MultiParamTypeClasses           #-}
{-# LANGUAGE PartialTypeSignatures           #-}
{-# LANGUAGE PatternSynonyms                 #-}
{-# LANGUAGE PolyKinds                       #-}
{-# LANGUAGE RankNTypes                      #-}
{-# LANGUAGE ScopedTypeVariables             #-}
{-# LANGUAGE TemplateHaskell                 #-}
{-# LANGUAGE TypeApplications                #-}
{-# LANGUAGE TypeFamilies                    #-}
{-# LANGUAGE TypeInType                      #-}
{-# LANGUAGE TypeOperators                   #-}
{-# LANGUAGE TypeSynonymInstances            #-}
{-# LANGUAGE UndecidableInstances            #-}
{-# LANGUAGE ViewPatterns                    #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module TTT.Core (
    Piece(..), SPiece()
  , GameOver(..), SGameOver
  , Board, BoardSym0
  , Sing(SPX, SPO, SGOWin, SGOCats)
  , altP, AltP, sAltP
  , lines, Lines, sLines
  , emptyBoard, EmptyBoard, sEmptyBoard
  , placeBoard, PlaceBoard, sPlaceBoard
  , boardOver, BoardOver, sBoardOver
  , Pick(..), pick
  , InPlay(..)
  , StateInPlay, StateInPlaySym0, StateInPlaySym1, StateInPlaySym2
  , GameState(..), Update(..), Coord(..)
  , play
  ) where

import           Data.Kind
import           Data.List hiding                (lines)
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.List
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Combinator.Singletons
import           Prelude hiding                  (lines)
import           TTT.Combinator
import           Type.Family.Nat

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

  placeBoard :: N -> N -> Piece -> Board -> Board
  placeBoard Z     j p (x:xs) = setIx j (Just p) x : xs
  placeBoard (S n) j p (x:xs) =                  x : placeBoard n j p xs

  (<|>) :: Maybe a -> Maybe a -> Maybe a
  Just x  <|> _ = Just x
  Nothing <|> y = y

  winLine :: [Maybe Piece] -> Maybe Piece
  winLine [] = Nothing
  winLine (Nothing:_) = Nothing
  winLine (Just x:xs) = if all (== Just x) xs
    then Just x
    else Nothing

  fullLine :: [Maybe Piece] -> Bool
  fullLine []           = True
  fullLine (Nothing:_ ) = False
  fullLine (Just _ :xs) = fullLine xs

  findMaybe :: (a -> Maybe b) -> [a] -> Maybe b
  findMaybe _ []     = Nothing
  findMaybe f (x:xs) = f x <|> findMaybe f xs

  boardOver :: Board -> Maybe GameOver
  boardOver b = (GOWin <$> findMaybe winLine (lines b))
            <|> if all fullLine b
                  then Just GOCats
                  else Nothing
  |])

data Pick :: N -> N -> Board -> Type where
    PickValid  :: Sel i b row     -> Sel j row 'Nothing  -> Pick i j b
    PickPlayed :: Sel i b row     -> Sel j row ('Just p) -> Sing p -> Pick i j b
    PickOoBX   :: OutOfBounds i b ->                        Pick i j b
    PickOoBY   :: Sel i b row     -> OutOfBounds j row   -> Pick i j b

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

data InPlay :: Board -> Type where
    InPlay :: (BoardOver b ~ 'Nothing) => InPlay b

data Coord :: Board -> Maybe Piece -> (N, N) -> Type where
    Coord :: Sel i b   row
          -> Sel j row p
          -> Coord b p '(i, j)

data Update :: (N, N) -> Piece -> Board -> Board -> Type where
    Update :: Coord b 'Nothing '(i, j)
           -> Sing p
           -> Update '(i, j) p b (PlaceBoard i j p b)

-- | Last played, and current board
data GameState :: Piece -> Board -> Type where
    GSStart  :: GameState p EmptyBoard
    GSUpdate :: InPlay b1
             -> Update ij p        b1 b2
             -> GameState p        b1
             -> GameState (AltP p)    b2

type StateInPlay p b = (GameState p b, InPlay b)
genDefunSymbols [''StateInPlay]

play
    :: forall b i j row p. ()
    => InPlay b
    -> Sel i b    row
    -> Sel j row 'Nothing
    -> Sing p
    -> GameState p b
    -> GameState (AltP p) (PlaceBoard i j p b)
play r i j p = GSUpdate r (Update (Coord i j) p)

