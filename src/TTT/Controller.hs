{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module TTT.Controller (
    Controller
  , priController
  , randController
  , validMoves
  ) where

import           Control.Monad.Primitive
import           Control.Monad.Trans.Reader
import           Data.Foldable
import           Data.Singletons
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           TTT.Core
import           Type.Family.Nat
import qualified Data.Map                           as M
import qualified System.Random.MWC                  as MWC

type Move b = Σ (N, N) (TyCon (Coord b 'Nothing))

type Controller m p = forall b. Sing b -> m (Maybe (Move b))

priController
    :: Applicative m
    => [(N, N)]
    -> Controller m p
priController xs b = pure $ asum (map (uncurry (go b)) xs)
  where
    go :: Sing b -> N -> N -> Maybe (Σ (N, N) (TyCon (Coord b 'Nothing)))
    go b' (FromSing i) (FromSing j) = case pick i j b' of
      PickValid i' j' -> Just $ STuple2 i j :&: Coord i' j'
      _               -> Nothing

randController
    :: PrimMonad m
    => Controller (ReaderT (MWC.Gen (PrimState m)) m) p
randController b
    | M.null vm = pure Nothing
    | otherwise = do
        i <- MWC.uniformR (0, M.size vm - 1) =<< ask
        pure . Just . snd $ M.elemAt i vm
  where
    vm = validMoves b

validMoves :: Sing b -> M.Map (N, N) (Move b)
validMoves b = M.fromList $ do
    (FromSing i, row) <- zip (iterate S Z) (FromSing b)
    (FromSing j, _  ) <- zip (iterate S Z) row
    PickValid i' j'   <- pure $ pick i j b
    pure ( (FromSing i, FromSing j)
         , STuple2 i j :&: Coord i' j'
         )
