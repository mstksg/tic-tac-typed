{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Nat (
    N(..), SN, Sing(SZ, SS)
  , addN, AddN, sAddN
  , LT(..)
  -- * Defun
  , ZSym0, SSym0, SSym1
  , AddNSym0, AddNSym1, AddNSym2
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.TH

$(singletons [d|
  data N = Z | S N
    deriving (Show, Eq, Ord)


  addN :: N -> N -> N
  addN Z     m = m
  addN (S n) m = S (addN n m)
  |])

data LT :: N -> N -> Type where
    LTZ :: LT 'Z n
    LTS :: LT n m -> LT ('S n) ('S m)
