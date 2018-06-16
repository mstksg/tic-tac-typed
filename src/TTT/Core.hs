{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
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
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module TTT.Core (
    Piece(..), SPiece()
  , Mode(..), SMode
  , Sing(SPX, SPO, SMPlay, SMStop)
  , altP, AltP, sAltP
  , lines, Lines, sLines
  , Board
  , emptyBoard, sEmptyBoard, EmptyBoard
  , Victory, Full, BoardWon
  , GameState(..)
  , StoppedGame, StoppedGameSym0, StoppedGameSym1, StoppedGameSym2
  , initGameState
  , Pick(..), pick
  , PlayResult(..)
  , play
  , PlaceBoard, sPlaceBoard, placeBoard
  , placeSel
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding  (Any)
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Combinator.Singletons
import           Data.Type.Index
import           Data.Type.Product
import           Prelude hiding                  (lines)
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

  type Board = [[Maybe Piece]]

  emptyBoard :: Board
  emptyBoard = [ [Nothing, Nothing, Nothing]
               , [Nothing, Nothing, Nothing]
               , [Nothing, Nothing, Nothing]
               ]
  |])

data Winner :: k -> [Maybe k] -> Type where
    W :: Uniform ('Just a ': as) -> Winner a ('Just a ': as)

type Victory b = Σ Piece (FlipSym2 (TyCon2 Winner) b)
genDefunSymbols [''Victory]

type Full       = Prod (Prod IsJust)
type BoardWon b = Any VictorySym0 (Lines b)

full
    :: Sing b
    -> Decision (Full b)
full = decideAll (decideAll isJust)


victory :: Sing as -> Decision (Victory as)
victory ss = case uniform ss of
    Proved u -> case ss of
      SNil               -> Disproved $ \case
        _ :&: w -> case w of {}
      SNothing `SCons` _ -> Disproved $ \case
        _ :&: w -> case w of {}
      SJust x  `SCons` _ -> Proved $ x :&: W u
    Disproved v -> Disproved $ \case
      _ :&: W u -> v u

boardWon :: Sing b -> Decision (BoardWon b)
boardWon = decideAny victory . sLines

data GameState :: Mode -> Board -> Type where
    GSVictory :: Any (TyCon1 (Winner p)) (Lines b)
              -> GameState ('MStop ('Just p)) b
    GSCats    :: Refuted (BoardWon b)
              -> Full b
              -> GameState ('MStop 'Nothing) b
    GSInPlay  :: Refuted (BoardWon b)
              -> Refuted (Full b)
              -> GameState ('MPlay p) b

type StoppedGame b s = GameState ('MStop s) b
genDefunSymbols [''StoppedGame]

gameState
    :: forall b p. ()
    => Sing b
    -> Either (GameState ('MPlay p) b)
              (Σ _ (StoppedGameSym1 b))
gameState b = case boardWon b of
    Proved (Any i (x :&: w)) ->
      Right $ SJust x :&: GSVictory (Any i w)
    Disproved notwon -> case full b of
      Proved filled ->
        Right $ SNothing :&: GSCats notwon filled
      Disproved notfilled ->
        Left $ GSInPlay notwon notfilled

emptyBoardNoWin :: Refuted (BoardWon EmptyBoard)
emptyBoardNoWin = undefined

emptyBoardNoFull :: Refuted (Full EmptyBoard)
emptyBoardNoFull = undefined

initGameState :: GameState ('MPlay 'PX) EmptyBoard
initGameState = GSInPlay emptyBoardNoWin emptyBoardNoFull

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
  |])

placeSel
    :: forall b i j p row. ()
    => Sel i b    row
    -> Sel j row 'Nothing
    -> Sing p
    -> Sing b
    -> Sing (PlaceBoard i j p b)
placeSel = \case
    SelZ -> \j p -> \case
      r `SCons` rs -> setSel j (SJust p) r `SCons` rs
    SelS i -> \j p -> \case
      r `SCons` rs ->                    r `SCons` placeSel i j p rs

data PlayResult :: Piece -> Board -> Type where
    PRInPlay  :: GameState ('MPlay p) b -> PlayResult p b
    PRStopped :: Sing s -> GameState ('MStop s) b -> PlayResult p b

play
    :: forall (b :: [[Maybe Piece]]) b' i j row p. (b' ~ PlaceBoard i j p b)
    => Sel i b    row
    -> Sel j row 'Nothing
    -> Sing p
    -> Sing b
    -> PlayResult (AltP p) b'
play i j p b = case gameState @b' @(AltP p) (placeSel i j p b) of
    Left gs          -> PRInPlay  gs
    Right (s :&: gs) -> PRStopped s gs


