{-# LANGUAGE MultiParamTypeClasses #-}
module SDCC (T, mu, eta, up, com, CanFlowTo, H, L) where

data T l a = T a

eta :: a -> T l a
eta = T

mu :: T l (T l a) -> T l a
mu (T a) = a

up :: CanFlowTo l l' => T l a -> T l' a
up (T a) = T a

com :: T l (T l' a) -> T l' (T l a)
com (T (T a)) = T (T a)

-- Choice of lattice
data H
data L

class Flows l l' => CanFlowTo l l'
instance CanFlowTo L L
instance CanFlowTo L H
instance CanFlowTo H H
class Flows l l'
instance Flows L L
instance Flows L H
instance Flows H H
