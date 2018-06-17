{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}

module TTT.Controller.Minimax (
    minimaxController
  , minimaxController'
  , RankRes(..)
  ) where

import           Control.Monad
import           Control.Monad.Primitive
import           Control.Monad.Reader
import           Data.Foldable
import           Data.Kind
import           Data.Ord
import           Data.Semigroup
import           Data.Singletons
import           Data.Singletons.Prelude hiding  (Min, Max)
import           Data.Singletons.Sigma
import           Data.Singletons.TH hiding       (Min, Max)
import           Data.Type.Combinator.Singletons
import           TTT.Controller
import           TTT.Core
import           Type.Family.Nat
import qualified Control.Foldl                   as F
import qualified Data.Vector                     as V
import qualified System.Random.MWC               as MWC
import qualified System.Random.MWC.Distributions as MWC

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

minimaxController'
    :: (PrimMonad m, MonadReader (MWC.Gen (PrimState m)) m)
    => N
    -> Controller m p
minimaxController' n CC{..} = do
    Option mm <-  minimax' _ccBoard _ccInPlay _ccPlayer _ccGameState n
    pure $ do
      Arg (RR res) m <- getMax <$> mm
      guard $ res /= Just (GOWin (FromSing (sAltP _ccPlayer)))
      pure m

minimax'
    :: forall p b m. (PrimMonad m, MonadReader (MWC.Gen (PrimState m)) m)
    => Sing b
    -> InPlay b
    -> Sing p
    -> GameState p b
    -> N
    -> m (Option (Max (Arg (RankRes p) (Move b))))
minimax' b r p g (FromSing n) = fst <$> pickMMTree p mmTree
  where
    mmTree = buildMMTree b r p g (SS n)

data SomeBranch :: N -> Board -> Piece -> (N, N) -> Type where
    SB :: MMTree n (PlaceBoard i j p b) (AltP p)
       -> Coord b 'Nothing '(i, j)
       -> SomeBranch n b p '(i, j)

data MMTree :: N -> Board -> Piece -> Type where
    MMCutoff   :: (BoardOver b ~ 'Nothing)
               => MMTree 'Z b p
    MMGameOver :: (BoardOver b ~ 'Just s)
               => Sing s
               -> MMTree n b p
    MMBranch   :: (BoardOver b ~ 'Nothing)
               => [Σ (N, N) (TyCon (SomeBranch n b p))]
               -> MMTree ('S n) b p

buildMMTree
    :: forall p b n. ()
    => Sing b
    -> InPlay b
    -> Sing p
    -> GameState p b
    -> Sing n
    -> MMTree n b p
buildMMTree b InPlay p g = \case
    SZ   -> MMCutoff
    SS n -> MMBranch . toList $ go n <$> validMoves b
  where
    go  :: Sing n'
        -> Move b
        -> Σ (N, N) (TyCon (SomeBranch n' b p))
    go n' (STuple2 i j :&: c@(Coord i' j')) = (STuple2 i j :&:) . flip SB c $ case sBoardOver b' of
        SNothing -> buildMMTree b' InPlay (sAltP p) g' n'
        SJust s  -> MMGameOver s
      where
        b' = sPlaceBoard i j p b
        g' = play InPlay i' j' p g

pickMMTree
    :: forall n b p m. (PrimMonad m, MonadReader (MWC.Gen (PrimState m)) m)
    => Sing p
    -> MMTree n b p
    -> m (Option (ArgMax (RankRes p) (Move b)), Sing (BoardOver b))
pickMMTree p = \case
    MMCutoff     -> pure (Option Nothing, SNothing)
    MMGameOver s -> pure (Option Nothing, SJust s )
    MMBranch bs  -> do
      bs' <- MWC.uniformShuffle (V.fromList bs) =<< ask
      res <- withSingI p $
        F.foldM (F.sink go) bs'
      pure (res, SNothing)
  where
    go  :: Σ (N, N) (TyCon (SomeBranch n' b p))
        -> m (Option (ArgMax (RankRes p) (Move b)))
    go (ij :&: SB m c) = Option . Just . Max . flip Arg (ij :&: c) . RR <$> do
      (Option r, o) <- pickMMTree (sAltP p) m
      pure $ case r of
        Just (Max (Arg (RR r') _)) -> r'
        Nothing                    -> FromSing o

getArg :: Arg a b -> a
getArg (Arg x _) = x

