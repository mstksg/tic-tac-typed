{-# LANGUAGE BlockArguments       #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Primitive
import           Control.Monad.Reader
import           Control.Monad.Trans.Except
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Lens
import           Data.Type.Predicate
import           Data.Type.Predicate.Logic
import           Data.Type.Predicate.Param
import           TTT.Controller
import           TTT.Controller.Console
import           TTT.Controller.Minimax
import           TTT.Core
import qualified System.Random.MWC          as MWC

data StateInPlay :: Piece ~> Predicate Board
type instance Apply StateInPlay p = TyPred (GameState p) &&& InPlay

playerX
    :: (MonadIO m, MonadReader (MWC.Gen (PrimState m)) m, PrimMonad m)
    => Controller m 'PX
playerX = consoleController

playerO
    :: (MonadIO m, MonadReader (MWC.Gen (PrimState m)) m, PrimMonad m)
    => Controller m 'PO
playerO = faulty 0.1 $ minimaxController cats
  where
    cats = S (S (S (S (S Z))))

data Exit = EForfeit Piece
          | EGameOver Result

main :: IO ()
main = MWC.withSystemRandom \g -> do
    Left (b,e) <- flip runReaderT g
                . runExceptT
                . chainForever (runGame playerX playerO) $
       STuple2 sing sing :&: (GSStart, startInPlay)
    putStrLn "Game over!"
    putStrLn $ displayBoard b
    putStrLn $ case e of
      EForfeit  p          -> "Forfeit by " ++ show p
      EGameOver ResCats    -> "Cat's game :("
      EGameOver (ResWin w) -> "Winner: " ++ show w

type EndoM m a = a -> m a

chainForever :: Monad m => EndoM m a -> EndoM m a
chainForever f = foldr (>=>) pure (repeat f)

runGame
    :: Monad m
    => Controller m 'PX
    -> Controller m 'PO
    -> EndoM (ExceptT (Board, Exit) m)
             (Σ (Piece, Board) (UncurrySym1 StateInPlay))
runGame cX cO (STuple2 p b :&: (g, r)) = case p of
    SPX -> do
      b' :&: (g', r') <- runController SPX cX (b :&: (g, r))
      pure $ STuple2 SPO b' :&: (g', r')
    SPO -> do
      b' :&: (g', r') <- runController SPO cO (b :&: (g, r))
      pure $ STuple2 SPX b' :&: (g', r')

runController
    :: Monad m
    => Sing p
    -> Controller m p
    -> Σ Board (StateInPlay @@ p)
    -> ExceptT (Board, Exit) m (Σ Board (StateInPlay @@ AltP p))
runController p c (b :&: (g, r)) = do
    move <- lift $ c CC { _ccBoard = b
                        , _ccInPlay = r
                        , _ccGameState = g
                        , _ccPlayer = p
                        }
    case move of
      Nothing -> throwE (FromSing b, EForfeit (FromSing p))
      Just (STuple2 i j :&: Coord i' j') -> do
        let b' = sPlaceBoard i j p b
            g' = play r i' j' p g
        case search @GameOver b' of
          Proved (s :&: _) -> throwE (FromSing b', EGameOver (FromSing s))
          Disproved m      -> pure $ b' :&: (g', m)
