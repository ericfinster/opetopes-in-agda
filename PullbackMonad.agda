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
    open _⇛_

    J : Set
    J = Σ I X

    PbP : Poly J J
    PbP = record { 
      γ = λ { (i , x) → ⟦ P ⟧ X i } ; 
      ρ = λ { ((i , x) , (c , φ)) → ρ P (i , c) } ; 
      τ = λ { (((i , x) , c , φ) , p) → (τ P ((i , c) , p)) , (φ p) } }

    pb-η : IdP J ⇛ PbP
    pb-η = record { 
      γ-map = λ { (i , x) tt → (γ-map η i tt , (λ p → transport! X {!unit-type-coh i!} x)) } ; 
      ρ-eqv = {!!} ; 
      τ-coh = {!!} }

      where open UnitLemmas P η

    pb-μ : PbP ⊚ PbP ⇛ PbP
    pb-μ = {!!}

    open UnitLemmas {J} PbP pb-η
    open AssocLemmas {J} PbP pb-μ

    postulate

      -- Not sure why the implicit argument resolution seems to not work here ...
      pb-unit-leaf-law : {j : J} (c : γ PbP j) → mult {j} (unit-leaf-decor {j} c) == c
      pb-unit-root-law : {j : J} (c : γ PbP j) → mult {j} (unit-root-decor {j} c) == c

      pb-assoc-law : {j : J} (c : γ (PbP ⊚ PbP ⊚ PbP) j) → 
                     mult {j} (mult-left {j} c) == mult {j} (mult-right {j} (decor-assoc-right j c))

    PbM : PolyMonad J
    PbM = record
            { P = PbP
            ; η = pb-η
            ; μ = pb-μ
            ; unit-leaf-law = λ {j} c → pb-unit-leaf-law {j} c
            ; unit-root-law = λ {j} c → pb-unit-root-law {j} c
            ; assoc-law = λ {j} c → pb-assoc-law {j} c
            }
