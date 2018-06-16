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
  , GameLog(..), Update(..)
  , boardOver, BoardOver, sBoardOver
  , initGameLog
  , InPlay(..)
  , emptyBoardNoFull
  , emptyBoardNoWin
  ) where

import           Data.Kind
import           Data.List hiding                     (lines)
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.List
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Combinator.Singletons
import           Data.Type.Index
import           Data.Type.Product
import           Prelude hiding                       (lines)
import           TTT.Combinator hiding                (Any)
import           Type.Family.Nat
import qualified TTT.Combinator                       as TTT

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

data Winner :: Piece -> [Maybe Piece] -> Type where
    W :: Uniform ('Just a ': as) -> Winner a ('Just a ': as)

type Victory b = Σ Piece (FlipSym2 (TyCon Winner) b)
genDefunSymbols [''Victory]

type Full       = Prod (Prod IsJust)
type BoardWon b = TTT.Any VictorySym0 (Lines b)

-- To disproe "any", prove that no possible example is true, out of all
-- eight possible lines
emptyBoardNoWin :: Refuted (BoardWon EmptyBoard)
emptyBoardNoWin = \case
    TTT.Any i (_ :&: W _) -> case i of
      IS (IS (IS (IS (IS (IS (IS (IS s))))))) -> case s of {}

-- To disprove "all", just find a single counter example
emptyBoardNoFull :: Refuted (Full EmptyBoard)
emptyBoardNoFull = \case
    x :< _ -> case x of
      y :< _ -> case y of
        {}

-- initGameState :: GameState ('MPlay 'PX) EmptyBoard
-- initGameState = GSInPlay emptyBoardNoWin emptyBoardNoFull

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

data GameLog :: Board -> Type where
    GLStart  :: GameLog b
    GLUpdate :: InPlay b1
             -> Update i j p b1 b2
             -> GameLog      b1
             -> GameLog      b2

initGameLog :: GameLog EmptyBoard
initGameLog = GLStart

play
    :: forall b i j row p. ()
    => InPlay b
    -> Sel i b    row
    -> Sel j row 'Nothing
    -> Sing p
    -> GameLog b
    -> GameLog (PlaceBoard i j p b)
play r i j p = GLUpdate r (Update i j p)

