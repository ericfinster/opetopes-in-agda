--
--  FreeMonad.agda - The free monad on a polynomial
--
--  Eric Finster
--

open import Prelude
open import Polynomial
open import PolynomialMonad

module FreeMonad where

  module FreeM (I : Set) (P : Poly I I) where
    
    open Poly
    open _≃_

    FmP : Poly I I
    FmP = record { 
            γ = W P ; 
            ρ = λ { (i , w) → leafOf w } ; 
            τ = λ { ((i , w) , l) → leafType l } 
          }

    fm-η : IdP I ⇛ FmP
    fm-η = record { 
             γ-map = λ i c → leaf i ; 
             ρ-eqv = λ i c → id-equiv ⊤ ;
             τ-coh = λ i c p → idp
           }

    {-# TERMINATING #-}
    fm-graft : (i : I) → γ (FmP ⊚ FmP) i → γ FmP i
    fm-graft i (leaf .i , φ) = φ tt
    fm-graft i (node .i (c , ψ) , φ) = 
      node i (c , (λ p₀ → fm-graft (τ P ((i , c) , p₀)) (ψ p₀ , (λ p₁ → φ (p₀ , p₁)))))

    {-# TERMINATING #-}
    fm-grafting-eqv : (i : I) (c : γ (FmP ⊚ FmP) i) → ρ (FmP ⊚ FmP) (i , c) ≃ ρ FmP (i , fm-graft i c)
    fm-grafting-eqv i (leaf .i , φ) = Σ-eqv-base (ρ FmP (i , (φ tt)))
    fm-grafting-eqv i (node .i (c , ψ) , φ) = 
      Σ-eqv-inv (ρ P (i , c)) _ _ (λ p → fm-grafting-eqv (τ P ((i , c) , p)) (ψ p , (λ p₀ → φ (p , p₀)))) ⊙ (Σ-eqv-lift _ _ _)

    {-# TERMINATING #-}
    fm-type-coh : (i : I) (c : γ (FmP ⊚ FmP) i) (p : ρ (FmP ⊚ FmP) (i , c)) →
                  τ (FmP ⊚ FmP) ((i , c) , p) ==
                  τ FmP ((i , fm-graft i c) , f (fm-grafting-eqv i c) p)
    fm-type-coh i (leaf .i , φ) (p₀ , p₁) = idp
    fm-type-coh i (node .i (c , ψ) , φ) ((p , l₀) , l₁) = 
      leafType l₁ =⟨ fm-type-coh (τ P ((i , c) , p)) (ψ p , (λ p₀ → φ (p , p₀))) (l₀ , l₁)  ⟩ 
      leafType (f (fm-grafting-eqv (τ P ((i , c) , p)) (ψ p , (λ p₀ → φ (p , p₀)))) (l₀ , l₁)) ∎
  
    fm-μ : FmP ⊚ FmP ⇛ FmP
    fm-μ = record { 
             γ-map = fm-graft ; 
             ρ-eqv = fm-grafting-eqv ; 
             τ-coh = fm-type-coh 
           }

  --   Fm : PolyMonad I
  --   Fm = record { P = FmP ; η = fm-η ; μ = fm-μ }
