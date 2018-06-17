{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}

module TTT.Controller.Minimax (
    minimaxController
  , RankRes(..)
  ) where

import           Control.Monad
import           Control.Monad.Primitive
import           Control.Monad.Reader
import           Data.Kind
import           Data.Ord
import           Data.Semigroup
import           Data.Singletons
import           Data.Singletons.Prelude hiding  (Min, Max)
import           Data.Singletons.Sigma
import           Data.Type.Combinator.Singletons
import           Debug.Trace
import           TTT.Controller
import           TTT.Core
import           Type.Family.Nat
import qualified Control.Foldl                   as F
import qualified System.Random.MWC               as MWC

newtype RankRes (p :: Piece) = RR { getRR :: Maybe GameOver }
  deriving (Show, Eq)

-- | lose < cats < in play < win
instance SingI p => Ord (RankRes p) where
    compare = comparing (rank . getRR)
      where
        rank :: Maybe GameOver -> Int
        rank = \case
          Nothing     -> 2
          Just GOCats -> 1
          Just (GOWin p)
            | p == FromSing (sing @p) -> 3
            | otherwise               -> 0

minimaxController
    :: (PrimMonad m, MonadReader (MWC.Gen (PrimState m)) m)
    => N
    -> Controller m p
minimaxController n CC{..} = do
    Option mm <-  minimax _ccBoard _ccInPlay _ccPlayer _ccGameState n
    pure $ do
      Arg (RR res) m <- getMax <$> mm
      guard $ res /= Just (GOWin (FromSing (sAltP _ccPlayer)))
      pure m

-- TODO: use Tree, cata, ana?
-- TODO: if maximum is loss, forfeit
minimax
    :: forall p b m. (PrimMonad m, MonadReader (MWC.Gen (PrimState m)) m)
    => Sing b
    -> InPlay b
    -> Sing p
    -> GameState p b
    -> N
    -> m (Option (Max (Arg (RankRes p) (Move b))))
minimax b r p g n = do
    moves <- shuffledValidMoves b =<< ask
    withSingI p  $
      F.foldM (F.sink go) (snd <$> moves)
  where
    go :: Move b -> m (Option (Max (Arg (RankRes p) (Move b))))
    go m@(STuple2 i j :&: Coord i' j') = do
      res <- case sBoardOver b' of
        SNothing -> case n of
          Z    -> pure @m . pure @Option $ Nothing
          S n' -> fmap (getRR . getArg . getMax) <$>
            minimax b' InPlay (sAltP p) g' n'
        SJust s -> pure @m . pure @Option $ Just (FromSing s)
      pure $ Max . flip Arg m . RR <$> res
      where
        b' = sPlaceBoard i j p b
        g' = play r i' j' p g

getArg :: Arg a b -> a
getArg (Arg x _) = x
