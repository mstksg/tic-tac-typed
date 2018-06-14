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
  , Victory(..), SomeVictory(..)
  , Full, BoardWon
  , GameState(..)
  , Pick(..), pick
  , play
  ) where

import           Data.Dependent.Sum
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude.List hiding  (Sum)
import           Data.Singletons.Prelude.Maybe hiding (IsJust)
import           Data.Singletons.TH
import           Data.Type.Index
import           Data.Type.Product
import           Data.Type.Sum
import           Prelude hiding                       (lines)
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

  emptyBoard :: [[Maybe Piece]]
  emptyBoard = [ [Nothing, Nothing, Nothing]
               , [Nothing, Nothing, Nothing]
               , [Nothing, Nothing, Nothing]
               ]
  |])

data Victory :: k -> [Maybe k] -> Type where
    V :: Uniform ('Just a) as -> Victory a as

data SomeVictory :: [Maybe k] -> Type where
    SV :: Sing a -> Uniform ('Just a) as -> SomeVictory as

type Full       = Prod (Prod IsJust)
type BoardWon b = Sum SomeVictory (Lines b)

full
    :: Sing b
    -> Decision (Full b)
full = decideAll (decideAll isJust)

someVictory
    :: forall k (as :: [Maybe k]). SDecide k
    => Sing as
    -> Decision (SomeVictory as)
someVictory ss = case uniform ss of
    Proved (SU SNothing u) -> Disproved $ \case
      SV _ UZ     -> case u of {}
      SV _ (US _) -> case u of {}
    Proved (SU (SJust s) u) -> Proved $ SV s u
    Disproved v -> Disproved $ \case
      SV s u -> v (SU (SJust s) u)

boardWon
    :: forall k (b :: [[Maybe k]]). SDecide k
    => Sing b
    -> Decision (BoardWon b)
boardWon = decideAny someVictory . sLines

data GameState :: Mode -> [[Maybe Piece]] -> Type where
    GSVictory :: Sum (Victory p) (Lines b)
              -> GameState ('MStop ('Just p)) b
    GSCats    :: Refuted (BoardWon b)
              -> Full b
              -> GameState ('MStop 'Nothing) b
    GSInPlay  :: Refuted (BoardWon b)
              -> Refuted (Full b)
              -> GameState ('MPlay p) b

gameState
    :: Sing b
    -> (GameState ('MPlay p) b -> r)
    -> (forall j. GameState ('MStop j) b -> r)
    -> r
gameState b f g = case boardWon b of
    Proved won -> withSum won $ \i (SV _ v) ->
      g $ GSVictory (injectSum i (V v))
    Disproved notwon -> case full b of
      Proved filled ->
        g $ GSCats notwon filled
      Disproved notfilled ->
        f $ GSInPlay notwon notfilled

data Pick :: [[Maybe Piece]] -> Type where
    PickValid  :: Index b row -> Index row 'Nothing  -> Pick b
    PickPlayed :: Index b row -> Index row ('Just p) -> Pick b
    PickOoBX   :: N           -> N -> Pick b
    PickOoBY   :: Index b row -> N -> Pick b

pick
    :: N
    -> N
    -> Sing b
    -> Pick b
pick i j b = case nIndex i b of
    Nothing           -> PickOoBX i j
    Just (row :=> i') -> case nIndex j row of
      Nothing -> PickOoBY i' j
      Just (p :=> j') -> case p of
        SNothing -> PickValid  i' j'
        SJust _  -> PickPlayed i' j'

place
    :: forall (b :: [[Maybe Piece]]) row. ()
    => Index b row
    -> Index row 'Nothing
    -> Piece
    -> Sing b
    -> [[Maybe Piece]]
place i j p = (mapIx (indexN i) . mapIx (indexN j)) (const (Just p))
            . fromSing

play
    :: forall (b :: [[Maybe Piece]]) row p r. ()
    => Index b row
    -> Index row 'Nothing
    -> Sing p
    -> Sing b
    -> (forall b'  . Sing b' -> GameState ('MPlay (AltP p)) b' -> r)
    -> (forall b' j. Sing b' -> GameState ('MStop j       ) b' -> r)
    -> r
play i j (fromSing->p) b f g = withSomeSing (place i j p b) $ \b' ->
    gameState b' (f b') (g b')

-- TODO: can Play return a b' with a known `(Index b' row, Index row ('Just p))`?
-- but do we need to?
