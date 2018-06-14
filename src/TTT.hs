{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module TTT (
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude.List hiding  (Sum)
import           Data.Singletons.Prelude.Maybe hiding (IsJust)
import           Data.Singletons.TH
import           Data.Type.Index
import           Data.Type.Product
import           Data.Type.Sum
import           Data.Type.Vector
import           Prelude hiding                       (lines)
import           Type.Class.Known
import           Type.Family.Nat

$(singletons [d|
  data Piece = PX | PO
    deriving Eq

  alt :: Piece -> Piece
  alt PX = PO
  alt PO = PX

  data Mode  = MPlay Piece
             | MStop (Maybe Piece)

  lines :: [[a]] -> [[a]]
  lines [[x1,y1,z1], [x2,y2,z2], [x3,y3,z3]]
    = [ [x1,y1,z1], [x2,y2,z2], [x3,y3,z3]
      , [x1,x2,x3], [y1,y2,y3], [z1,z2,z3]
      , [x1,y2,z3], [x3,y2,z1]
      ]
  |])

data Uniform :: k -> [k] -> Type where
    UZ :: Uniform a '[a]
    US :: Uniform a as -> Uniform a (a ': as)

data SomeUniform :: [k] -> Type where
    SU :: Sing a -> Uniform a as -> SomeUniform as

data Victory :: k -> [Maybe k] -> Type where
    V :: Uniform ('Just a) as -> Victory a as

data SomeVictory :: [Maybe k] -> Type where
    SV :: Sing a -> Uniform ('Just a) as -> SomeVictory as

data IsJust :: Maybe k -> Type where
    IsJust :: IsJust ('Just a)

instance Known IsJust ('Just a) where
    known = IsJust

type Full       = Prod (Prod IsJust)
type BoardWon b = Sum SomeVictory (Lines b)

isJust :: Sing a -> Decision (IsJust a)
isJust = \case
    SNothing -> Disproved $ \case {}
    SJust _  -> Proved IsJust

decideAll
    :: forall f as. ()
    => (forall a. Sing a -> Decision (f a))
    -> Sing as
    -> Decision (Prod f as)
decideAll f = go
  where
    go  :: Sing bs -> Decision (Prod f bs)
    go  = \case
      SNil         -> Proved Ø
      s `SCons` ss -> case f s of
        Proved p    -> case go ss of
          Proved ps    -> Proved $ p :< ps
          Disproved vs -> Disproved $ \case
            _ :< ps -> vs ps
        Disproved v -> Disproved $ \case
            p :< _ -> v p

full
    :: Sing b
    -> Decision (Full b)
full = decideAll (decideAll isJust)

uniform
    :: forall k (as :: [k]). SDecide k
    => Sing as
    -> Decision (SomeUniform as)
uniform = \case
    SNil            -> Disproved $ \case
      SU _ u -> case u of {}
    sx `SCons` SNil -> Proved $ SU sx UZ
    sx `SCons` ss@(_ `SCons` _) -> case uniform ss of
      Proved (SU sy us) -> case sx %~ sy of
        Proved Refl -> Proved $ SU sx (US us)
        Disproved v -> Disproved undefined
      Disproved vs -> Disproved $ \case
        SU s (US u) -> vs $ SU s u

someVictory
    :: forall k (as :: [Maybe k]). SDecide k
    => Sing as
    -> Decision (SomeVictory as)
someVictory ss = case uniform ss of
    Proved (SU SNothing u) -> Disproved $ \case
      SV _ UZ     -> case u of {}
      SV _ (US _) -> case u of {}
    Proved (SU (SJust s) u) -> Proved $ SV s u
    Disproved v -> Disproved $ \case
      SV s u -> v (SU (SJust s) u)

decideAny
    :: forall f as. ()
    => (forall a. Sing a -> Decision (f a))
    -> Sing as
    -> Decision (Sum f as)
decideAny f = go
  where
    go  :: Sing bs -> Decision (Sum f bs)
    go  = \case
      SNil         -> Disproved $ \case {}
      s `SCons` ss -> case f s of
        Proved p    -> Proved $ InL p
        Disproved v -> case go ss of
          Proved ps    -> Proved $ InR ps
          Disproved vs -> Disproved $ \case
            InL p  -> v  p
            InR ps -> vs ps

withSum
    :: forall f as r. ()
    => Sum f as
    -> (forall a. Index as a -> f a -> r)
    -> r
withSum = \case
    InL x  -> \f -> f IZ x
    InR xs -> \f -> withSum xs (f . IS)

boardWon
    :: forall k (b :: [[Maybe k]]). SDecide k
    => Sing b
    -> Decision (BoardWon b)
boardWon = decideAny someVictory . sLines

data GameState :: Mode -> [[Maybe Piece]] -> Type where
    GSVictory :: Sum (Victory p) (Lines b)
              -> GameState ('MStop ('Just p)) b
    GSCats    :: Refuted (BoardWon b)
              -> Full b
              -> GameState ('MStop 'Nothing) b
    GSInPlay  :: Refuted (BoardWon b)
              -> Refuted (Full b)
              -> GameState ('MPlay p) b

gameState
    :: Sing b
    -> (GameState ('MPlay p) b -> r)
    -> (forall j. GameState ('MStop j) b -> r)
    -> r
gameState b f g = case boardWon b of
    Proved won -> withSum won $ \i (SV _ v) ->
      g $ GSVictory (injectSum i (V v))
    Disproved notwon -> case full b of
      Proved filled ->
        g $ GSCats notwon filled
      Disproved notfilled ->
        f $ GSInPlay notwon notfilled

overIx
    :: forall k (as :: [k]) (a :: k). SingKind k
    => Index as a
    -> (Sing a -> Demote k)
    -> Sing as
    -> Demote [k]
overIx = \case
    IZ -> \f -> \case
      s `SCons` SNil -> [f s]
      s `SCons` ss@(_ `SCons` _) -> f s : fromSing ss
    IS i -> \f -> \case
      s `SCons` SNil -> [fromSing s]
      s `SCons` ss@(_ `SCons` _) -> fromSing s : overIx i f ss

place
    :: forall (b :: [[Maybe Piece]]) row. ()
    => Index b row
    -> Index row 'Nothing
    -> Piece
    -> Sing b
    -> [[Maybe Piece]]
place i j p = overIx i (overIx j (const (Just p)))

play
    :: forall (b :: [[Maybe Piece]]) row p r. ()
    => Index b row
    -> Index row 'Nothing
    -> Sing p
    -> Sing b
    -> (forall b'  . Sing b' -> GameState ('MPlay (Alt p)) b' -> r)
    -> (forall b' j. Sing b' -> GameState ('MStop j      ) b' -> r)
    -> r
play i j (fromSing->p) b f g = withSomeSing (place i j p b) $ \b' ->
    gameState b' (f b') (g b')
