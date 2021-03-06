{-# LANGUAGE BlockArguments         #-}
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
{-# LANGUAGE TypeOperators          #-}
{-# OPTIONS_GHC -Wno-orphans        #-}

module TTT.Controller.Minimax (
    minimaxController
  , minimaxController'
  , RankRes(..)
  ) where

import           Control.Monad
import           Control.Monad.Primitive
import           Control.Monad.Reader
import           Data.Foldable
import           Data.GADT.Compare
import           Data.Kind
import           Data.Ord
import           Data.Semigroup
import           Data.Singletons
import           Data.Singletons.Prelude hiding  (Min, Max)
import           Data.Singletons.Sigma
import           Data.Singletons.TH hiding       (Min, Max)
import           Data.Type.Lens
import           Data.Type.Predicate.Param
import           TTT.Controller
import           TTT.Core
import qualified Control.Foldl                   as F
import qualified Data.Dependent.Map              as DM
import qualified Data.Vector                     as V
import qualified System.Random.MWC               as MWC
import qualified System.Random.MWC.Distributions as MWC

newtype RankRes (p :: Piece) = RR { getRR :: Maybe Result }
  deriving (Show, Eq)

-- | lose < cats < in play < win
instance SingI p => Ord (RankRes p) where
    compare = comparing (rank . getRR)
      where
        rank :: Maybe Result -> Int
        rank = \case
          Nothing      -> 2
          Just ResCats -> 1
          Just (ResWin p)
            | p == FromSing (sing @p) -> 3
            | otherwise               -> 0

-- | This minimax implementation is "verified" in the sense that it cannot
-- make any illegal moves.  We sort of get this "for free".  It is also
-- verified that we will rank and sort the pieces correctly (assuming the
-- Ord instance is sound) depending on who is playing.
minimaxController
    :: (PrimMonad m, MonadReader (MWC.Gen (PrimState m)) m)
    => N
    -> Controller m p
minimaxController n CC{..} = do
    Option mm <-  minimax _ccBoard _ccInPlay _ccPlayer _ccGameState n
    pure . maybeToCResp $ do
      Arg (RR res) m <- getMax <$> mm
      guard $ res /= Just (ResWin (FromSing (sAltP _ccPlayer)))
      pure m

minimax
    :: forall p b m. (PrimMonad m, MonadReader (MWC.Gen (PrimState m)) m)
    => Sing b
    -> InPlay @@ b
    -> Sing p
    -> GameState p b
    -> N
    -> m (Option (Max (Arg (RankRes p) (Move @@ b))))
minimax b r p g n = do
    moves <- shuffledValidMoves b =<< ask
    withSingI p  $
      F.foldM (F.sink go) (snd <$> moves)
  where
    go :: Move @@ b -> m (Option (Max (Arg (RankRes p) (Move @@ b))))
    go m@(STuple2 i j :&: c) = do
      res <- case searchTC b' of
        Proved (s :&: _) -> pure @m. pure @Option $ Just (FromSing s)
        Disproved v      -> case n of
          Z    -> pure @m . pure @Option $ Nothing
          S n' -> fmap (getRR . getArg . getMax) <$>
            minimax b' v (sAltP p) g' n'
      pure $ Max . flip Arg m . RR <$> res
      where
        b' = sPlaceBoard i j p b
        g' = play r c g

-- | This minimax implementation is "more verified" than the original one.
-- In addition to the verifications of the original one, we verify that the
-- search algorithm doesn't go further than the number of steps, and also
-- that at each step we are being consistent with the board and possible
-- moves.
--
-- However, it is not a "verified AI" in that it can still make the wrong
-- choice in the end.  The only thing verified really is that it interprets
-- the information it sees correctly.
minimaxController'
    :: (PrimMonad m, MonadReader (MWC.Gen (PrimState m)) m)
    => N
    -> Controller m p
minimaxController' n CC{..} = do
    Option mm <-  minimax' _ccBoard _ccInPlay _ccPlayer _ccGameState n
    pure . maybeToCResp $ do
      Arg (RR res) m <- getMax <$> mm
      guard $ res /= Just (ResWin (FromSing (sAltP _ccPlayer)))
      pure m

minimax'
    :: forall p b m. (PrimMonad m, MonadReader (MWC.Gen (PrimState m)) m)
    => Sing b
    -> InPlay @@ b
    -> Sing p
    -> GameState p b
    -> N
    -> m (Option (Max (Arg (RankRes p) (Move @@ b))))
minimax' b r p g (FromSing n) = fst <$> pickMMTree p mmTree
  where
    mmTree = buildMMTree b r p g (SS n)

data SomeBranch :: N -> Board -> Piece -> (N, N) -> Type where
    SB :: MMTree n (PlaceBoard i j p b) (AltP p)
       -> Coord '(i, j) b 'Nothing
       -> SomeBranch n b p '(i, j)

data MMTree :: N -> Board -> Piece -> Type where
    MMCutoff   :: InPlay @@ b
               -> MMTree 'Z b p
    MMGameOver :: GameOver b @@ s
               -> Sing s
               -> MMTree n b p
    MMBranch   :: InPlay @@ b
               -> DM.DMap Sing (SomeBranch n b p)
               -> MMTree ('S n) b p

buildMMTree
    :: forall p b n. ()
    => Sing b
    -> InPlay @@ b
    -> Sing p
    -> GameState p b
    -> Sing n
    -> MMTree n b p
buildMMTree b gm p g = \case
    SZ   -> MMCutoff gm
    SS n -> MMBranch gm . DM.fromAscList . toList $ go n <$> validMoves b
  where
    go  :: Sing n'
        -> Move @@ b
        -> DM.DSum Sing (SomeBranch n' b p)
    go n' (STuple2 i j :&: c) = (STuple2 i j DM.:=>) . flip SB c $
        case searchTC b' of
          Proved (s :&: m) -> MMGameOver m s
          Disproved m      -> buildMMTree b' m (sAltP p) g' n'
      where
        b' = sPlaceBoard i j p b
        g' = play gm c g

pickMMTree
    :: forall n b p m. (PrimMonad m, MonadReader (MWC.Gen (PrimState m)) m)
    => Sing p
    -> MMTree n b p
    -> m (Option (ArgMax (RankRes p) (Move @@ b)), Decision (Found GameOver @@ b))
pickMMTree p = \case
    MMCutoff   m   -> pure (Option Nothing, Disproved m     )
    MMGameOver m s -> pure (Option Nothing, Proved $ s :&: m)
    MMBranch m bs -> do
      bs' <- MWC.uniformShuffle (V.fromList (DM.toList bs)) =<< ask
      res <- withSingI p $
        F.foldM (F.sink go) bs'
      pure (res, Disproved m)
  where
    go  :: DM.DSum Sing (SomeBranch n' b p)
        -> m (Option (ArgMax (RankRes p) (Move @@ b)))
    go (ij DM.:=> SB m c) = Option . Just . Max . flip Arg (ij :&: c) . RR <$> do
      (Option r, o) <- pickMMTree (sAltP p) m
      pure $ case r of
        Just (Max (Arg (RR r') _)) -> r'
        Nothing                    -> case o of
          Proved (o' :&: _) -> Just . FromSing $ o'
          Disproved _       -> Nothing

getArg :: Arg a b -> a
getArg (Arg x _) = x

instance SDecide k => GEq (Sing :: k -> Type) where
    geq x y = case x %~ y of
      Proved p    -> Just p
      Disproved _ -> Nothing
