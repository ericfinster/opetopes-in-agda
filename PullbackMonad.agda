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
  
    open PolyMonad 
    open Poly
    open _⇛_

    PM : Poly I I
    PM = P M

    ηM : IdP I ⇛ PM
    ηM = η M

    μM : PM ⊚ PM ⇛ PM
    μM = μ M

    J : Set
    J = Σ I X

    PbP : Poly J J
    PbP = record { 
      γ = λ { (i , x) → ⟦ PM ⟧ X i } ; 
      ρ = λ { ((i , x) , (c , φ)) → ρ PM (i , c) } ; 
      τ = λ { (((i , x) , c , φ) , p) → (τ PM ((i , c) , p)) , (φ p) } }

    pb-η : IdP J ⇛ PbP
    pb-η = record { 
      γ-map = λ { (i , x) tt → unit-cons i x } ; 
      ρ-eqv = λ { (i , x) tt → ρ-eqv ηM i tt } ; 
      τ-coh = λ { (i , x) tt tt → type-coh i x } }

      where open UnitLemmas PM ηM

            unit-cons : (i : I) (x : X i) → γ PbP (i , x)
            unit-cons i x = (unit-at i , (λ p → transport! X (unit-place-type-coh p) x))

            -- should be provable without K, but I doubt the multiplication case will be ...
            type-coh : (i : I) (x : X i) → (i , x) == τ PbP (((i , x) , unit-cons i x) , unit-place-at i)
            type-coh i x = 
              (i , x) =⟨ Σ-transport! (unit-type-coh i) ⟩ 
              (τ PM ((i , unit-at i) , unit-place-at i) , transport! X (unit-type-coh i) x) 
                =⟨ transport!-coh X (unit-K i) x |in-ctx (λ x₀ → (τ PM ((i , unit-at i) , unit-place-at i) , x₀)) ⟩ 
              (τ PM ((i , unit-at i) , unit-place-at i) , transport! X (unit-place-type-coh (unit-place-at i)) x) =⟨ idp ⟩ 
              τ PbP (((i , x) , unit-cons i x) , ρ-map ηM tt tt) ∎ 

    module _ where

      open AssocLemmas PM μM

      pb-mult : (j : J) → γ (PbP ⊚ PbP) j → γ PbP j
      pb-mult (i , x) ((c , φ) , ψ) = {!mult!}

    pb-μ : PbP ⊚ PbP ⇛ PbP
    pb-μ = record { 
      γ-map = pb-mult ; 
      ρ-eqv = {!!} ; 
      τ-coh = {!!} }

    open UnitLemmas PbP pb-η
    open AssocLemmas PbP pb-μ

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
