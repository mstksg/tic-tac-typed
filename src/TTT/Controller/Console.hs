{-# LANGUAGE BlockArguments   #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TypeApplications #-}

module TTT.Controller.Console (
    consoleController
  , displayBoard
  ) where

import           Control.Monad.IO.Class
import           Data.Char
import           Data.List
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.Sigma
import           Data.Type.Lens
import           Data.Type.Predicate
import           TTT.Controller
import           TTT.Core
import qualified Data.Map                     as M
import qualified System.Console.Haskeline     as H

repeatUntil
    :: Monad m
    => m (Maybe a)
    -> m a
repeatUntil act = go
  where
    go = maybe go pure =<< act

-- | Will never allow any invalid moves.
consoleController
    :: MonadIO m
    => Controller m p
consoleController CC{..} = liftIO . repeatUntil $ do
    putStrLn $ displayBoard (FromSing _ccBoard)
    putStrLn $ "Move for " ++ show (FromSing _ccPlayer)
    ml <- H.runInputT H.defaultSettings $ H.getInputLine "> "
    case ml of
      Nothing -> pure $ Just CRQuit
      Just l  -> case parseCoord l of
        Nothing -> case map toLower l of
          'q':_ -> pure $ Just CRQuit
          _     -> Nothing <$ putStrLn "No parse. Try again. (q or Ctrl+D to quit)"
        Just (FromSing i, FromSing j) -> case proveTC (STuple3 i j _ccBoard) of
          PickValid c  -> pure . Just . CRMove $ STuple2 i j :&: c
          PickPlayed{} -> Nothing <$ putStrLn "Spot is already played. Try again."
          PickOoBX{}   -> Nothing <$ putStrLn "Out of bounds. Try again."
          PickOoBY{}   -> Nothing <$ putStrLn "Out of bounds. Try again."

parseCoord :: String -> Maybe (N, N)
parseCoord (j:i:_) = (,) <$> M.lookup i rowMap <*> M.lookup (toUpper j) colMap
parseCoord _       = Nothing

colMap :: M.Map Char N
colMap = M.fromList $ zip ['A'..'Z'] (iterate S Z)
rowMap :: M.Map Char N
rowMap = M.fromList $ zip ['1'..'9'] (iterate S Z)

displayBoard :: Board -> String
displayBoard = unlines
             . ("   A   B   C ":)
             . intersperse "  ---+---+---"
             . zipWith (\n l -> show @Int n ++ " " ++ l) [1..]
             . map (intercalate "|" . map (pad1 . slotChar))
  where
    pad1 c = [' ', c, ' ']
    slotChar Nothing   = ' '
    slotChar (Just PX) = 'X'
    slotChar (Just PO) = 'O'
