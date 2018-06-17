{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PartialTypeSignatures  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}

import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Reader
import           Data.Char
import           Data.List
import           Data.Singletons
import           Control.Monad.Primitive
import           Control.Monad.Reader
import           Data.Singletons.Prelude
import           Data.Singletons.Sigma
import           TTT.Controller
import           TTT.Controller.Console
import           TTT.Controller.Minimax
import           TTT.Core
import           Type.Family.Nat
import qualified Data.Map                   as M
import qualified System.Random.MWC          as MWC

playerX :: MonadIO m => Controller m 'PX
playerX = consoleController

playerY :: (MonadIO m, MonadReader (MWC.Gen (PrimState m)) m, PrimMonad m)
        => Controller m 'PO
-- playerY = minimaxController (S (S (S (S (S Z)))))   -- force cats
playerY = minimaxController (S (S (S Z)))

data Exit = EForfeit Piece
          | EGameOver GameOver

main :: IO ()
main = MWC.withSystemRandom $ \g -> do
    Left (b,e) <- flip runReaderT g
                . runExceptT
                . chainForever (runGame playerX playerY) $
       STuple2 sing sing :&: (GSStart @'PX, InPlay)
    putStrLn "Game over!"
    putStrLn $ displayBoard b
    putStrLn $ case e of
      EForfeit  p         -> "Forfeit by " ++ show p
      EGameOver GOCats    -> "Cat's game :("
      EGameOver (GOWin w) -> "Winner: " ++ show w

type EndoM m a = a -> m a

chainForever :: Monad m => EndoM m a -> EndoM m a
chainForever f = foldr (>=>) pure (repeat f)

runGame
    :: Monad m
    => Controller m 'PX
    -> Controller m 'PO
    -> EndoM (ExceptT (Board, Exit) m)
             (Σ (Piece, Board) (UncurrySym1 StateInPlaySym0))
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
    -> Σ Board (StateInPlaySym1 p)
    -> ExceptT (Board, Exit) m (Σ Board (StateInPlaySym1 (AltP p)))
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
        case sBoardOver b' of
          SNothing -> pure   $ b' :&: (g', InPlay)
          SJust s  -> throwE (FromSing b', EGameOver (FromSing s))
