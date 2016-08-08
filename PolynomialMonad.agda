{-# OPTIONS --without-K #-}

open import HoTT

open import Polynomial
open import CartesianMorphism
open import PolyMisc

module PolynomialMonad where

  record PolyMonad {ℓ} (I : Type ℓ) : Type (lsucc ℓ) where
    field

      P : Poly I I
  
      η : IdP I ⇝ P
      μ : P ⊚ P ⇝ P

      -- P ⇝ IdP I ⊚ P ⇝ P ⊚ P ⇝ P
      η-left-law : ⊚-unit-l P ▶ (η ∥ poly-id P) ▶ μ ≈ poly-id P

      -- P ⇝ P ⊚ IdP I ⇝ P ⊚ P ⇝ P
      η-right-law : ⊚-unit-r P ▶ (poly-id P ∥ η) ▶ μ ≈ poly-id P

      -- (P ⊚ P) ⊚ P ⇝ P ⊚ (P ⊚ P) ⇝ P ⊚ P ⇝ P
      μ-assoc-law : ⊚-assoc-r P P P ▶ (poly-id P ∥ μ) ▶ μ ≈ (μ ∥ poly-id P) ▶ μ 

      -- The other associative law (which should be provable ...)
      -- μ-assoc-law' : ⊚-assoc-l P P P ▶ (μ ∥ poly-id P) ▶ μ ≈ (poly-id P ∥ μ) ▶ μ

  module _ {ℓ} {I : Type ℓ} (M : PolyMonad I) where

    open PolyMonad M
    
    η-cns : (i : I) → γ P i
    η-cns i = ⟪ η ⟫ lt

    η-plc : (i : I) → ρ P (η-cns i)
    η-plc i = ⟪ η ⟫↓ lt
    
    η-unfold : (i : I) → (δ : ⟦ P ⟧⟦ η-cns i ≺ γ P ⟧) →
               ⟪ μ ⟫ (η-cns i , δ) == δ (η-plc i) [ γ P ↓ ⟪ η ⟫↓= lt ]
    η-unfold i δ = {!!}

       where α : ⟪ ⊚-unit-r P ▶ (poly-id P ∥ η) ▶ μ ⟫ (δ (η-plc i)) == (δ (η-plc i))
             α = γ≈ (η-right-law (δ (η-plc i))) 

             β : ⟪ ⊚-unit-r P ▶ (poly-id P ∥ η) ▶ μ ⟫ (δ (η-plc i)) == (δ (η-plc i)) 
             β = ⟪ ⊚-unit-r P ▶ (poly-id P ∥ η) ▶ μ ⟫ (δ (η-plc i)) =⟨ idp ⟩
                 ⟪ μ ⟫ (⟪ ⊚-unit-r P ▶ (poly-id P ∥ η) ⟫ (δ (η-plc i))) =⟨ idp ⟩
                 ⟪ μ ⟫ (⟪ poly-id P ∥ η ⟫ (⟪ ⊚-unit-r P ⟫ (δ (η-plc i)))) =⟨ idp ⟩ 
                 ⟪ μ ⟫ (⟪ poly-id P ∥ η ⟫ (lt , λ _ → δ (η-plc i))) =⟨ idp ⟩
                 ⟪ μ ⟫ (⟪ η ⟫ lt , ⟪ poly-id P ∣ η ⟫⇕ (cst (δ (η-plc i)))) =⟨ α ⟩ 
                 (δ (η-plc i))  ∎

             blorp : ⟦ P ⟧⟦ ⟪ η ⟫ {τ P (η-plc i)} lt ≺ γ P ⟧
             blorp = ⟪ poly-id P ∣ η ⟫⇕ (cst (δ (η-plc i)))
    
             bleep : ⟦ P ⟧⟦ ⟪ η ⟫ {i} lt ≺ γ P ⟧
             bleep = δ 

             lemma : δ == ⟪ poly-id P ∣ η ⟫⇕ (cst (δ (η-plc i))) [ (λ j → ⟦ P ⟧⟦ ⟪ η ⟫ {j} lt ≺ γ P ⟧) ↓ ⟪ η ⟫↓= lt ]
             lemma = ↓-Π-in (λ {p₀} {p₁} r → {!!})

             fred : δ (η-plc i) == ⟪ poly-id P ∣ η ⟫⇕ (cst (δ (η-plc i))) (⟪ η ⟫↓ lt) [ γ P ↓ ⟪ η ⟫↓= lt ]
             fred = ⟪ poly-id P ∣ η ⟫⇕-coh (cst (δ (η-plc i))) lt

             wilma : δ (η-plc i) == transport (γ P) (⟪ η ⟫↑= (⟪ η ⟫↓ lt)) (δ (η-plc i)) [ γ P ↓ ⟪ η ⟫↓= lt ]
             wilma = ⟪ poly-id P ∣ η ⟫⇕-coh (cst (δ (η-plc i))) lt
