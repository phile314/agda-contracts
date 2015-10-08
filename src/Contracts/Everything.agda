module Contracts.Everything where

-- The internal syntax + applying contracts + deriving types
open import Contracts.Base
-- Surface syntax for contracts
open import Contracts.SSyn

-- Partial isomorphisms for nat<=>int and vec<=>list
open import Contracts.Isos

-- Partial isomorphism for witness objects/refined types/dependent pairs
open import Contracts.Witness

-- Examples using the internal syntax
open import Contracts.BaseExample

-- Examples using the surface syntax
open import Contracts.example
open import Contracts.example2
