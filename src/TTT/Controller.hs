{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TypeFamilies     #-}

module TTT.Controller (
    Controller, Move, CContext(..)
  , priorityController
  , randomController
  , validMoves
  , shuffledValidMoves
  , faulty
  ) where

import           Control.Monad.Primitive
import           Control.Monad.Reader
import           Data.Foldable
import           Data.Singletons
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Nat
import           TTT.Core
import qualified Data.Map                        as M
import qualified Data.Vector                     as V
import qualified System.Random.MWC               as MWC
import qualified System.Random.MWC.Distributions as MWC

type Move b = Σ (N, N) (TyCon (Coord b 'Nothing))

data CContext p b = CC { _ccBoard     :: Sing b
                       , _ccInPlay    :: InPlay b
                       , _ccGameState :: GameState p b
                       , _ccPlayer    :: Sing p
                       }

type Controller m p = forall b. CContext p b -> m (Maybe (Move b))

validMoves :: Sing b -> M.Map (N, N) (Move b)
validMoves b = M.fromList $ do
    (FromSing i, row) <- zip (iterate S Z) (FromSing b)
    (FromSing j, _  ) <- zip (iterate S Z) row
    PickValid i' j'   <- pure $ pick i j b
    pure ( (FromSing i, FromSing j)
         , STuple2 i j :&: Coord i' j'
         )

shuffledValidMoves
    :: PrimMonad m
    => Sing b
    -> MWC.Gen (PrimState m)
    -> m [((N, N), Move b)]
shuffledValidMoves b g = V.toList
    <$> MWC.uniformShuffle (V.fromList . M.toList . validMoves $ b) g

-- | Picks the first valid move in the given list
priorityController
    :: Applicative m
    => [(N, N)]
    -> Controller m p
priorityController xs CC{..} = pure $ asum (map (uncurry (go _ccBoard)) xs)
  where
    go :: Sing b -> N -> N -> Maybe (Move b)
    go b' (FromSing i) (FromSing j) = case pick i j b' of
      PickValid i' j' -> Just $ STuple2 i j :&: Coord i' j'
      _               -> Nothing

-- | Picks a random move
randomController
    :: (PrimMonad m, MonadReader (MWC.Gen (PrimState m)) m)
    => Controller m p
randomController CC{..}
    | M.null vm = pure Nothing
    | otherwise = do
        i <- MWC.uniformR (0, M.size vm - 1) =<< ask
        pure . Just . snd $ M.elemAt i vm
  where
    vm = validMoves _ccBoard

-- | Return a controller that, some percentage of the time, picks randomly
-- instead.
faulty
    :: (PrimMonad m, MonadReader (MWC.Gen (PrimState m)) m)
    => Double
    -> Controller m p
    -> Controller m p
faulty r f cc = do
    s <- MWC.uniform =<< ask
    if s <= r
      then randomController cc
      else f cc

