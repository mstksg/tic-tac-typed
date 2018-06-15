{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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

module TTT.Core (
    Piece(..), SPiece()
  , Mode(..), SMode
  , Sing(SPX, SPO, SMPlay, SMStop)
  , altP, AltP, sAltP
  , lines, Lines, sLines
  , emptyBoard, sEmptyBoard, EmptyBoard
  , Victory(..)
  , Full, BoardWon
  , GameState(..), StoppedGame(..)
  , Pick(..), pick
  , play
  , PlaceBoard, sPlaceBoard, placeBoard
  , placeSel
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.TH
import           Data.Type.Combinator.Singletons
import           Data.Type.Conjunction
import           Data.Type.Product
import           Data.Type.Sum
import           Prelude hiding                          (lines)
import           TTT.Combinator
import           Type.Class.Higher
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

  emptyBoard :: [[Maybe Piece]]
  emptyBoard = [ [Nothing, Nothing, Nothing]
               , [Nothing, Nothing, Nothing]
               , [Nothing, Nothing, Nothing]
               ]
  |])

data Victory :: [Maybe k] -> Type where
    V :: Uniform ('Just a ': as) -> Victory ('Just a ': as)

data Winner :: k -> [Maybe k] -> Type where
    W :: Uniform ('Just a ': as) -> Winner a ('Just a ': as)

type Full       = Prod (Prod IsJust)
type BoardWon b = Sum Victory (Lines b)

full
    :: Sing b
    -> Decision (Full b)
full = decideAll (decideAll isJust)

victory
    :: forall k (as :: [Maybe k]). SDecide k
    => Sing as
    -> Decision (Victory as)
victory ss = case uniform ss of
    Proved u -> case ss of
      SNil               -> Disproved $ \case {}
      SNothing `SCons` _ -> Disproved $ \case {}
      SJust _  `SCons` _ -> Proved $ V u
    Disproved v -> Disproved $ \case
      V u -> v u

boardWon
    :: forall k (b :: [[Maybe k]]). SDecide k
    => Sing b
    -> Decision (BoardWon b)
boardWon = decideAny victory . sLines

data GameState :: Mode -> [[Maybe Piece]] -> Type where
    GSVictory :: Sum (Winner p) (Lines b)
              -> GameState ('MStop ('Just p)) b
    GSCats    :: Refuted (BoardWon b)
              -> Full b
              -> GameState ('MStop 'Nothing) b
    GSInPlay  :: Refuted (BoardWon b)
              -> Refuted (Full b)
              -> GameState ('MPlay p) b

data StoppedGame :: [[Maybe Piece]] -> Type where
    SG :: GameState ('MStop s) b -> StoppedGame b

type InPlayGame p = GameState ('MPlay (AltP p))

gameState
    :: forall b p. ()
    => Sing b
    -> Either (InPlayGame p b) (StoppedGame b)
gameState b = case boardWon b of
    Proved won -> withSum won $ \i (V v) ->
      Right . SG $ GSVictory (injectSum i (W v))
    Disproved notwon -> case full b of
      Proved filled ->
        Right . SG $ GSCats notwon filled
      Disproved notfilled ->
        Left $ GSInPlay notwon notfilled

type OutOfBounds n as = Refuted (Some (Sing :&: Sel n as))

listSel
    :: Sing n
    -> Sing as
    -> Decision (Some (Sing :&: Sel n as))
listSel = \case
    SZ -> \case
      SNil -> Disproved $ \case
        Some (_ :&: s) -> case s of {}
      s `SCons` _ -> Proved $ Some (s :&: SelZ)
    SS n -> \case
      SNil -> Disproved $ \case
        Some (_ :&: s) -> case s of {}
      _ `SCons` xs -> case listSel n xs of
        Proved (Some (y :&: s)) -> Proved (Some (y :&: SelS s))
        Disproved v -> Disproved $ \case
          Some (y :&: s) -> case s of
            SelS m -> v (Some (y :&: m))

data Pick :: N -> N -> [[Maybe Piece]] -> Type where
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
    Proved (Some (row :&: i')) -> case listSel j row of
      Proved (Some (p :&: j')) -> case p of
        SJust q  -> PickPlayed i' j' q
        SNothing -> PickValid i' j'
      Disproved v -> PickOoBY i' v
    Disproved v -> PickOoBX v

$(singletons [d|
  placeBoard :: N -> N -> Piece -> [[Maybe Piece]] -> [[Maybe Piece]]
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

play
    :: forall (b :: [[Maybe Piece]]) b' i j row p. (b' ~ PlaceBoard i j p b)
    => Sel i b    row
    -> Sel j row 'Nothing
    -> Sing p
    -> Sing b
    -> Either (InPlayGame (AltP p) b') (StoppedGame b')
play i j p b = gameState @b' @(AltP p) b'
  where
    b' = placeSel i j p b
