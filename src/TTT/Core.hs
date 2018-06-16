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
  , Mode(..), SMode
  , Sing(SPX, SPO, SMPlay, SMStop)
  , altP, AltP, sAltP
  , lines, Lines, sLines
  , Board, BoardSym0
  , emptyBoard, sEmptyBoard, EmptyBoard
  , InPlay(..), inPlay
  , Victory, Full, BoardWon
  , GameState(..)
  , StoppedGame, StoppedGameSym0, StoppedGameSym1, StoppedGameSym2
  , initGameState
  , Pick(..), pick
  , PlayResult(..)
  , play
  , PlaceBoard, sPlaceBoard, placeBoard
  , placeSel
  , play'
  , GameLog(..), Update(..)
  , boardMode, BoardMode, sBoardMode
  , boardModeInPlay
  , initGameLog
  ) where

import           Data.Kind
import           Data.List hiding                     (lines)
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.List
import           Data.Singletons.Prelude.Maybe hiding (IsJust)
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

  data Mode  = MPlay Piece
             | MStop (Maybe Piece)

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

data InPlay :: Mode -> Piece -> Type where
    InPlay :: InPlay ('MPlay p) p

inPlay :: Sing m -> Decision (Σ Piece (TyCon (InPlay m)))
inPlay = \case
    SMPlay p -> Proved $ p :&: InPlay
    SMStop _ -> Disproved $ \case
      _ :&: ip -> case ip of {}

data Winner :: Piece -> [Maybe Piece] -> Type where
    W :: Uniform ('Just a ': as) -> Winner a ('Just a ': as)

type Victory b = Σ Piece (FlipSym2 (TyCon Winner) b)
genDefunSymbols [''Victory]

type Full       = Prod (Prod IsJust)
type BoardWon b = TTT.Any VictorySym0 (Lines b)

full
    :: Sing b
    -> Decision (Full b)
full = decideAll (decideAll isJust)


victory
    :: forall (as :: [Maybe Piece]). ()
    => Sing as
    -> Decision (Victory as)
victory ss = case uniform ss of
    Proved u -> case ss of
      SNil               -> Disproved $ \case
        _ :&: w -> case w of {}
      SNothing `SCons` _ -> Disproved $ \case
        _ :&: w -> case w of {}
      SJust x  `SCons` _ -> Proved $ x :&: W u
    Disproved v -> Disproved $ \case
      _ :&: W u -> v u

boardWon
    :: forall (b :: Board). ()
    => Sing b
    -> Decision (BoardWon b)
boardWon = decideAny victory . sLines

data GameState :: Mode -> Board -> Type where
    GSVictory :: TTT.Any (TyCon (Winner p)) (Lines b)
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
    Proved (TTT.Any i (x :&: w)) ->
      Right $ SJust x :&: GSVictory (TTT.Any i w)
    Disproved notwon -> case full b of
      Proved filled ->
        Right $ SNothing :&: GSCats notwon filled
      Disproved notfilled ->
        Left $ GSInPlay notwon notfilled

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

  winLine :: [Maybe Piece] -> Maybe Piece
  winLine [] = Nothing
  winLine (Nothing:_) = Nothing
  winLine (Just x:xs) = if all (== Just x) xs
    then Just x
    else Nothing

  fullLine :: [Maybe Piece] -> Bool
  fullLine [] = True
  fullLine (Nothing:_ ) = False
  fullLine (Just _ :xs) = fullLine xs

  findMaybe :: (a -> Maybe b) -> [a] -> Maybe b
  findMaybe _ [] = Nothing
  findMaybe f (x:xs) = case f x of
    Nothing -> findMaybe f xs
    Just y  -> Just y

  boardMode :: Piece -> Board -> Mode
  boardMode p b = case findMaybe winLine (lines b) of
    Just w  -> MStop (Just w)
    Nothing -> if all fullLine b
      then MStop Nothing
      else MPlay p
  |])

boardModeInPlay
    :: Sing p
    -> Sing b
    -> InPlay (BoardMode p b) p'
    -> p :~: p'
boardModeInPlay p b InPlay = case sBoardMode p b of
    SMPlay p' -> case p %~ p' of
      Proved Refl -> Refl
      Disproved _ -> error "This should never happen, but GHC says it could?"
    -- -> Decision (InPlay (BoardMode p b) p)
-- boardModeInPlay = \case
    -- SPX -> \b -> case sBoardMode SPX b of
    --   SMPlay SPX -> Proved InPlay
    --   SMPlay SPO -> error "This should never happen, but GHC says it could?"
    --   SMStop _   -> Disproved $ \case {}
    -- SPO -> \b -> case sBoardMode SPO b of
    --   SMPlay SPX -> error "This should never happen, but GHC says it could?"
    --   SMPlay SPO -> Proved InPlay
    --   SMStop _   -> Disproved $ \case {}


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

data Update :: N -> N -> Piece -> Board -> Board -> Type where
    Update :: Sel i b   row
           -> Sel j row 'Nothing
           -> Update i j p b (PlaceBoard i j p b)

data GameLog :: Board -> Type where
    GLStart  :: GameLog b
    GLUpdate :: InPlay (BoardMode p b1) p
             -> Update i j p b1 b2
             -> GameLog      b1
             -> GameLog      b2

initGameLog :: GameLog EmptyBoard
initGameLog = GLStart

-- checkMode
--     :: Sing b
--     -> MPlay

-- data CheckMode :: Board -> Type where
--     CMPlay :: BoardMode p b :~: 'MPlay p -> CheckMode b
--     CMStop :: Sing s -> BoardMode p b :~: 'MStop s -> CHeckMode b

  -- winLine :: [Maybe Piece] -> Maybe Piece
  -- winLine [] = Nothing
  -- winLine (Nothing:xs) = Nothing
  -- winLine (Just x:xs)  = if all (== Just x) xs
  --   then Just x
  --   else Nothing

  -- fullLine :: [Maybe Piece] -> Bool
  -- fullLine [] = True
  -- fullLine (Nothing:_ ) = False
  -- fullLine (Just _ :xs) = fullLine xs

  -- findMaybe :: (a -> Maybe b) -> [a] -> Maybe b
  -- findMaybe _ [] = Nothing
  -- findMaybe f (x:xs) = case f x of
  --   Nothing -> findMaybe f xs
  --   Just y  -> Just y

  -- boardMode :: Piece -> Board -> Mode
  -- boardMode p b = case findMaybe winLine (lines b) of
  --   Just w  -> MStop (Just w)
  --   Nothing -> if all fullLine b
  --     then MStop Nothing
  --     else MPlay (altP p)

    -- GLUpdate :: BoardMode p b1 :~: 'MPlay p

play'
    :: forall b i j row p. ()
    => InPlay (BoardMode p b) p
    -> Sel i b    row
    -> Sel j row 'Nothing
    -> GameLog b
    -> GameLog (PlaceBoard i j p b)
play' r i j = GLUpdate r (Update i j)
