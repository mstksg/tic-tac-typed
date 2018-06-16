{-# LANGUAGE DataKinds              #-}
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
  ) where

import           Data.Kind
import           Data.Ord
import           Data.Semigroup
import           Data.Singletons
import           Data.Singletons.Prelude hiding (Min, Max)
import           Data.Singletons.Sigma
import           Data.Type.Combinator.Singletons
import           TTT.Controller
import           TTT.Core
import           Type.Family.Nat

newtype RankRes (p :: Piece) = RR { getRankRes :: Maybe GameOver }
  deriving (Show, Eq)

-- | lose < cats < in play < win
instance SingI p => Ord (RankRes p) where
    compare = comparing (rank . getRankRes)
      where
        rank :: Maybe GameOver -> Int
        rank = \case
          Nothing     -> 2
          Just GOCats -> 1
          Just (GOWin p)
            | p == FromSing (sing @p) -> 3
            | otherwise               -> 0

minimaxController
    :: Applicative m
    => N
    -> Controller m p
minimaxController n CC{..} = pure $ withSingI _ccPlayer $
    case minimax _ccBoard _ccInPlay _ccGameState MMLMin n of
      Option mm -> (\(Min (Arg _ m)) -> m) <$> mm

data MMLevel :: (Type -> Type) -> Type where
    MMLMax :: MMLevel Max
    MMLMin :: MMLevel Min

-- TODO: use Tree, cata, ana?
minimax
    :: forall p b m. SingI p
    => Sing b
    -> InPlay b
    -> GameState p b
    -> MMLevel m
    -> N
    -> Option (m (Arg (RankRes p) (Move b)))
minimax b r g l n = case l of
                      MMLMax -> foldMap go . validMoves $ b
                      MMLMin -> foldMap go . validMoves $ b
  where
    p :: Sing p
    p = sing
    go :: SingI p => Move b -> Option (m (Arg (RankRes p) (Move b)))
    go m@(STuple2 i j :&: Coord i' j') = mmLevel l . flip Arg m <$> rr
      where
        b' = sPlaceBoard i j p b
        g' = play r i' j' p g
        rr = RR <$> case sBoardOver b' of
          SNothing -> case n of
            Z    -> pure Nothing
            S n' -> withSingI (sAltP p) $
              case l of
                MMLMax -> (\(Min (Arg (RR o) _)) -> o) <$>
                  minimax @(AltP p) b' InPlay g' MMLMin n'
                MMLMin -> (\(Max (Arg (RR o) _)) -> o) <$>
                  minimax @(AltP p) b' InPlay g' MMLMax n'
          SJust s -> pure $ Just (FromSing s)

mmLevel :: MMLevel m -> a -> m a
mmLevel = \case
    MMLMax -> Max
    MMLMin -> Min

-- maxi
--     :: forall p b n. SingI p
--     => Sing b
--     -> InPlay b
--     -> GameState p b
--     -> N
--     -> Option (ArgMax (RankRes p) (Move b))
-- maxi b r g n = foldMap go . validMoves $ b
--   where
--     p :: Sing p
--     p = sing
--     go :: SingI p => Move b -> Option (Max (Arg (RankRes p) (Move b)))
--     go m@(STuple2 i j :&: Coord i' j') = Max . flip Arg m <$> rr
--       where
--         b' = sPlaceBoard i j p b
--         g' = play r i' j' p g
--         rr = RR <$> case sBoardOver b' of
--           SNothing -> case n of
--             Z   -> pure Nothing
--             S m -> withSingI (sAltP p) $
--               flip fmap (mini @(AltP p) b' InPlay g' m) $ \case
--                 Min (Arg (RR o) _) -> o
--           SJust s -> pure $ Just (FromSing s)

-- mini
--     :: forall p b n. SingI p
--     => Sing b
--     -> InPlay b
--     -> GameState p b
--     -> N
--     -> Option (ArgMin (RankRes p) (Move b))
-- mini = undefined
-- -- mini b r g n = selectMove b go
-- --   where
-- --     go :: SingI p => Move b -> Max (Arg (RankRes p) (Move b))
-- --     go m@(STuple2 i j :&: Coord i' j') = Max $ Arg rr m
-- --       where
-- --         b' = sPlaceBoard i j (sing @p) b
-- --         g' = play r i' j' (sing @p) g
-- --         rr = RR $ case sBoardOver b' of
-- --           SNothing -> case n of
-- --             Z   -> Nothing
-- --             S m -> _
-- --           SJust s -> Just $ FromSing s


-- case n of
--           Z   -> FromSing o
--           S m -> case o of
--             SNothing -> mini
    -- case play r i' j' p

      -- Just (STuple2 i j :&: Coord i' j') -> do
      --   let b' = sPlaceBoard i j p b
      --       g' = play r i' j' p g
      --   case sBoardOver b' of
      --     SNothing -> pure   $ b' :&: (g', InPlay)
      --     SJust s  -> throwE $ Right (FromSing s)

-- play
--     :: forall b i j row p. ()
--     => InPlay b
--     -> Sel i b    row
--     -> Sel j row 'Nothing
--     -> Sing p
--     -> GameState p b
--     -> GameState (AltP p) (PlaceBoard i j p b)
-- play r i j p = GSUpdate r (Update (Coord i j) p)


--             g' = play r i' j' p g
  -- boardOver :: Board -> Maybe GameOver
  -- boardOver b = (GOWin <$> findMaybe winLine (lines b))
  --           <|> if all fullLine b
  --                 then Just GOCats
  --                 else Nothing
    -- SZ ->
    --     $ validMoves b

--   SS SZ -> fmap ((\(Arg _ m) -> m) . getMax) . selectMove b $ _
--   -- (SS n) = _ $ selectMove b go
--   -- where
--   --   go = case n of
--   --     SZ -> _
--     -- go = case n of
--     --   SS SZ ->
--     -- SS (SS n) -> fmap (\(Arg _ m) -> m)
--     --            . getOption
--     --            . foldMap (\m -> )
--     --            $ validMoves b

-- type Move b = Σ (N, N) (TyCon (Coord b 'Nothing))

-- validMoves :: Sing b -> M.Map (N, N) (Move b)
-- validMoves b = M.fromList $ do
--     (FromSing i, row) <- zip (iterate S Z) (FromSing b)
--     (FromSing j, _  ) <- zip (iterate S Z) row
--     PickValid i' j'   <- pure $ pick i j b
--     pure ( (FromSing i, FromSing j)
--          , STuple2 i j :&: Coord i' j'
--          )

