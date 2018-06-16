{-# LANGUAGE PolyKinds  #-}
{-# LANGUAGE RankNTypes #-}

module TTT.Controller.Console (
    consoleController
  ) where

import           Control.Applicative
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Maybe
import           Data.Char
import           Data.Foldable
import           Data.List
import           Data.Maybe
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.Sigma
import           TTT.Controller
import           TTT.Core
import           Type.Family.Nat
import qualified Data.Map                  as M

repeatUntil
    :: Monad m
    => m (Maybe a)
    -> m a
repeatUntil = fmap fromJust . runMaybeT . asum . repeat . MaybeT

consoleController
    :: MonadIO m
    => Sing p
    -> Controller m p
consoleController p b = liftIO . repeatUntil $ do
    putStrLn $ displayBoard (FromSing b)
    putStrLn $ "Move for " ++ show (FromSing p)
    l <- getLine
    case parseCoord l of
      Nothing -> case map toLower l of
        'q':_ -> pure $ Just Nothing
        _     -> Nothing <$ putStrLn "No parse. Try again. (q to quit)"
      Just (FromSing i, FromSing j) -> case pick i j b of
        PickValid i' j' -> pure . Just . Just $ STuple2 i j :&: Coord i' j'
        PickPlayed{}    -> Nothing <$ putStrLn "Spot is already played. Try again."
        PickOoBX{}      -> Nothing <$ putStrLn "Out of bounds. Try again."
        PickOoBY{}      -> Nothing <$ putStrLn "Out of bounds. Try again."

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
             . zipWith ((++) . addNum) [1..]
             . map (intercalate "|" . map (pad1 . slotChar))
  where
    pad1 c = [' ', c, ' ']
    slotChar Nothing   = ' '
    slotChar (Just PX) = 'X'
    slotChar (Just PO) = 'O'
    addNum :: Int -> String
    addNum n = show n ++ " "
