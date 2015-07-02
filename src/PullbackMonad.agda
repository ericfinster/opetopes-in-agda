--
--  PullbackMonad.agda - The pullback of a polynomial monad
--
--  Eric Finster
--

open import Prelude
open import Polynomial
open import PolynomialMonad

module PullbackMonad where

  module Pullback (I : Set) (X : I → Set) (M : PolyMonad I) where
  
    open Poly
    open PolyMonad M

    J : Set
    J = Σ I X

    PbP : Poly J J
    PbP = record { 
      γ = λ { (i , x) → ⟦ P ⟧ X i } ; 
      ρ = λ { ((i , x) , (c , φ)) → ρ P (i , c) } ; 
      τ = λ { (((i , x) , c , φ) , p) → (τ P ((i , c) , p)) , (φ p) } }

  --   -- PbM : PolyMonad I
  --   -- PbM = {!!}
