{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE PartialTypeSignatures  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}

import           Data.Char
import           Data.List
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           TTT.Core
import           Type.Family.Nat
import qualified Data.Map                as M

data MoveError = MEPlaced
               | MEOutOfBounds
  deriving Show

type InPlayLog (p :: Piece) b = (GameLog b, InPlay b)
genDefunSymbols [''InPlayLog]

makeMove
    :: N
    -> N
    -> Sing p
    -> Σ Board (InPlayLogSym1 p)
    -> Either MoveError (Σ Board (TyCon GameLog))
makeMove (FromSing i) (FromSing j) p (b :&: (gl, r)) = case pick i j b of
    PickValid i' j' -> Right $ sPlaceBoard i j p b
                           :&: play r i' j' p gl
    PickPlayed{}    -> Left MEPlaced
    PickOoBX{}      -> Left MEOutOfBounds
    PickOoBY{}      -> Left MEOutOfBounds

main :: IO ()
main = gameLoop (STuple2 SPX sing :&: (initGameLog, InPlay))

gameLoop
    :: Σ (Piece, Board) (UncurrySym1 InPlayLogSym0)
    -> IO ()
gameLoop sgs0@(STuple2 p b :&: (gl, r)) = do
    putStrLn $ displayBoard (FromSing b)
    putStrLn $ "Move for " ++ show (FromSing p)
    c <- parseCoord <$> getLine
    case c of
      Nothing -> do
        putStrLn "No parse.  Try again."
        gameLoop sgs0
      Just (i, j) -> case makeMove i j p (b :&: (gl, r)) of
        Left e -> do
          putStrLn $ "Bad move: " ++ show e
          putStrLn "Try again."
          gameLoop sgs0
        Right (b' :&: gl') -> case sBoardOver b' of
          SNothing -> gameLoop $ STuple2 (sAltP p) b' :&: (gl', InPlay)
          SJust s -> do
            putStrLn $ displayBoard (FromSing b')
            putStrLn "Game Over!"
            putStrLn $ case s of
              SGOCats  -> "Cat's game :("
              SGOWin w -> "Winner: " ++ show (FromSing w)

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
