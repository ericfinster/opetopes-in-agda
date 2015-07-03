--
--  PolynomialMonad.agda - Indexed Polynomial Monads
--
--  Eric Finster
--

open import Prelude
open import Polynomial

module PolynomialMonad where

  module UnitLemmas {I : Set} (P : Poly I I) (η : IdP I ⇛ P) where

    open Poly 
    open _⇛_

    unit-at : (i : I) → γ P i
    unit-at i = γ-map η i tt

    unit-place-at : (i : I) → ρ P (i , unit-at i)
    unit-place-at i = ρ-map η tt tt

    unit-place-unique : {i : I} → (p : ρ P (_ , unit-at i)) → p == unit-place-at i
    unit-place-unique p = equiv-unit-has-all-paths (ρ P (_ , unit-at _)) (ρ-eqv η _ _) p _

    unit-type-coh : (i : I) → τ P (_ , unit-place-at i) == i
    unit-type-coh i = ! (τ-coh η i tt tt)

    unit-place-type-coh : {i : I} → (p : ρ P (_ , unit-at i)) → τ P (_ , p) == τ P (_ , unit-place-at i)
    unit-place-type-coh p = ap _ (unit-place-unique p)
  
    cons-to-unit-type : {i : I} → (p : ρ P (_ , unit-at i)) → γ P i → γ P (τ P (_ , p))
    cons-to-unit-type p = transport! (γ P) (unit-place-type-coh p ∙ unit-type-coh _)

    unit-leaf-decor : {i : I} → (c : γ P i) → γ (P ⊚ P) i
    unit-leaf-decor c = (c , λ p → unit-at _)

    unit-root-decor : {i : I} → (c : γ P i) → γ (P ⊚ P) i
    unit-root-decor c = (unit-at _ , λ p → cons-to-unit-type p c)

  module AssocLemmas {I : Set} (P : Poly I I) (μ : P ⊚ P ⇛ P) where

    open Poly
    open _⇛_

    mult : {i : I} → γ (P ⊚ P) i → γ P i
    mult d = γ-map μ _ d

    mult-left : {i : I} → γ ((P ⊚ P) ⊚ P) i → γ (P ⊚ P) i
    mult-left (c , φ) = c , (λ p → mult (φ p) )

    lift-place : {i : I} → {d : γ (P ⊚ P) i} → (p : ρ P (_ , mult d)) → ρ (P ⊚ P) (i , d)
    lift-place p = ρ-inv-map μ _ p

    lift-place-coh : {i : I} → {d : γ (P ⊚ P) i} → (p : ρ P (_ , mult d)) → 
                     τ (P ⊚ P) (_ , lift-place p) == τ P (_ , p)
    lift-place-coh p = 
      τ (P ⊚ P) (_ , lift-place p)           =⟨ τ-coh μ _ _ (lift-place p) ⟩ 
      τ P (_ ,  ρ-map μ _ (lift-place p))    =⟨ ρ-inv-right μ p |in-ctx (λ p₀ → τ P (_ , p₀)) ⟩ 
      τ P (_ , p) ∎

    -- This is possible not a good name.  What it says is that if you have a decoration on a two 
    -- level tree, then you have a decoration of the constructor you obtain by multiplying down
    -- the base tree.
    induced-decor : {i : I} → {d : γ (P ⊚ P) i} → (ψ : (p : ρ (P ⊚ P) (i , d)) → γ P (τ (P ⊚ P) ((i , d) , p))) → 
                                                    (p : ρ P (i , mult d)) → γ P (τ P ((i , mult d) , p))
    induced-decor ψ p = transport (γ P) (lift-place-coh p) (ψ (lift-place p))

    mult-right : {i : I} → γ (P ⊚ (P ⊚ P)) i → γ (P ⊚ P) i
    mult-right (d , ψ) = (mult d , induced-decor ψ)

    decor-assoc-right : (i : I) → γ ((P ⊚ P) ⊚ P) i → γ (P ⊚ (P ⊚ P)) i
    decor-assoc-right i (c , φ) = (c , (λ p → proj₁ (φ p))) , (λ { (p₀ , p₁) → proj₂ (φ p₀) p₁ })

    decor-assoc-left : (i : I) → γ (P ⊚ (P ⊚ P)) i → γ ((P ⊚ P) ⊚ P) i 
    decor-assoc-left i ((c , φ) , ψ) = c , (λ p₀ → (φ p₀) , (λ p₁ → ψ (p₀ , p₁)))

    assoc-decor-equiv : (i : I) → γ ((P ⊚ P) ⊚ P) i ≃ γ (P ⊚ (P ⊚ P)) i
    assoc-decor-equiv i = record { 
      f = decor-assoc-right i ;
      g = decor-assoc-left i ; 
      g-f = λ { (c , φ) → idp } ;
      f-g = λ { ((c , φ) , ψ) → idp } }

  record PolyMonad (I : Set) : Set₁ where

    field

      P : Poly I I
  
      η : IdP I ⇛ P
      μ : P ⊚ P ⇛ P

    open UnitLemmas P η
    open AssocLemmas P μ

    open Poly 

    field

      unit-leaf-law : {i : I} → (c : γ P i) → mult (unit-leaf-decor c) == c
      unit-root-law : {i : I} → (c : γ P i) → mult (unit-root-decor c) == c

      assoc-law : {i : I} → (c : γ ((P ⊚ P) ⊚ P) i) → 
                  mult (mult-left c) == mult (mult-right (decor-assoc-right i c))

