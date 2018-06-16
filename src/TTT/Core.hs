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
  , Sing(SPX, SPO, SGOWin, SGOCats)
  , altP, AltP, sAltP
  , lines, Lines, sLines
  , Board, BoardSym0
  , emptyBoard, sEmptyBoard, EmptyBoard
  , Pick(..), pick
  , PlaceBoard, sPlaceBoard, placeBoard
  , play
  , GameState(..), Update(..)
  , boardOver, BoardOver, sBoardOver
  , InPlay(..)
  ) where

import           Data.Kind
import           Data.List hiding                (lines)
import           Data.Singletons
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

  altP :: Piece -> Piece
  altP PX = PO
  altP PO = PX

  data GameOver = GOCats
                | GOWin Piece

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

$(singletons [d|
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

data InPlay :: Board -> Type where
    InPlay :: (BoardOver b ~ 'Nothing) => InPlay b

data Update :: N -> N -> Piece -> Board -> Board -> Type where
    Update :: Sel i b   row
           -> Sel j row 'Nothing
           -> Sing p
           -> Update i j p b (PlaceBoard i j p b)

-- | Last played, and current board
data GameState :: Piece -> Board -> Type where
    GSStart  :: GameState p EmptyBoard
    GSUpdate :: InPlay b1
             -> Update i j p        b1 b2
             -> GameState    p        b1
             -> GameState    (AltP p)    b2

play
    :: forall b i j row p. ()
    => InPlay b
    -> Sel i b    row
    -> Sel j row 'Nothing
    -> Sing p
    -> GameState p b
    -> GameState (AltP p) (PlaceBoard i j p b)
play r i j p = GSUpdate r (Update i j p)

