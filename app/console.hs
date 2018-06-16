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
import           Data.Singletons.Prelude
import           Data.Singletons.Sigma
import           TTT.Controller
import           TTT.Controller.Console
import           TTT.Core
import           Type.Family.Nat
import qualified Data.Map                   as M
import qualified System.Random.MWC          as MWC

playerX :: Controller IO 'PX
playerX = consoleController

playerY :: MWC.GenIO -> Controller IO 'PO
playerY g p = flip runReaderT g . randController p

runner :: MWC.GenIO
       -> EndoM (ExceptT (Either Piece GameOver) IO)
                (Σ (Piece, Board) (UncurrySym1 StateInPlaySym0))
runner g = runGame playerX (playerY g)

main :: IO ()
main = MWC.withSystemRandom $ \g -> do
    Left s <- runExceptT . foldr (>=>) pure (repeat (runner g)) $
       STuple2 sing sing :&: (GSStart @'PX, InPlay)
    putStrLn $ case s of
      Left p          -> "Forfeit by " ++ show p
      Right GOCats    -> "Cat's game :("
      Right (GOWin w) -> "Winner: " ++ show w

type EndoM m a = a -> m a

runGame
    :: Monad m
    => Controller m 'PX
    -> Controller m 'PO
    -> EndoM (ExceptT (Either Piece GameOver) m)
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
    -> ExceptT (Either Piece GameOver) m (Σ Board (StateInPlaySym1 (AltP p)))
runController p c (b :&: (g, r)) = do
    move <- lift $ c p b
    case move of
      Nothing -> throwE $ Left (FromSing p)
      Just (STuple2 i j :&: Coord i' j') -> do
        let b' = sPlaceBoard i j p b
            g' = play r i' j' p g
        case sBoardOver b' of
          SNothing -> pure   $ b' :&: (g', InPlay)
          SJust s  -> throwE $ Right (FromSing s)
