{-# LANGUAGE BlockArguments   #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module TTT.Controller (
    Controller, Move, CContext(..), CResponse(..), maybeToCResp
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
import           Data.Type.Lens
import           Data.Type.Predicate
import           Data.Type.Predicate.Param
import           TTT.Core
import qualified Data.Map                        as M
import qualified Data.Vector                     as V
import qualified System.Random.MWC               as MWC
import qualified System.Random.MWC.Distributions as MWC

data AvailableSpot :: ParamPred Board (N, N)
type instance Apply (AvailableSpot b) c = Coord c b 'Nothing

type Move = Found AvailableSpot

data CContext p b = CC { _ccBoard     :: Sing b
                       , _ccInPlay    :: InPlay @@ b
                       , _ccGameState :: GameState p b
                       , _ccPlayer    :: Sing p
                       }

data CResponse b = CRQuit
                 | CRMove (Move @@ b)

maybeToCResp :: Maybe (Move @@ b) -> CResponse b
maybeToCResp Nothing  = CRQuit
maybeToCResp (Just m) = CRMove m

type Controller m p = forall b. CContext p b -> m (CResponse b)

validMoves
    :: Sing b
    -> M.Map (N, N) (Move @@ b)
validMoves b = M.fromList do
    (FromSing i, row) <- zip (iterate S Z) (FromSing b)
    (FromSing j, _  ) <- zip (iterate S Z) row
    PickValid c       <- pure $ proveTC (STuple3 i j b)
    pure ( (FromSing i, FromSing j)
         , STuple2 i j :&: c
         )

shuffledValidMoves
    :: PrimMonad m
    => Sing b
    -> MWC.Gen (PrimState m)
    -> m [((N, N), Move @@ b)]
shuffledValidMoves b g = V.toList
    <$> MWC.uniformShuffle (V.fromList . M.toList . validMoves $ b) g

-- | Picks the first valid move in the given list
priorityController
    :: Applicative m
    => [(N, N)]
    -> Controller m p
priorityController xs CC{..} = pure 
                             . maybeToCResp
                             . asum
                             $ map (uncurry (go _ccBoard)) xs
  where
    go :: Sing b -> N -> N -> Maybe (Move @@ b)
    go b' (FromSing i) (FromSing j) = case proveTC (STuple3 i j b') of
      PickValid c -> Just $ STuple2 i j :&: c
      _           -> Nothing

-- | Picks a random move
randomController
    :: (PrimMonad m, MonadReader (MWC.Gen (PrimState m)) m)
    => Controller m p
randomController CC{..}
    | M.null vm = pure CRQuit
    | otherwise = do
        i <- MWC.uniformR (0, M.size vm - 1) =<< ask
        pure . CRMove . snd $ M.elemAt i vm
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

