{-# OPTIONS --without-K #-}

open import HoTT

open import Polynomial
open import CartesianMorphism
open import PolyMisc

open ADMIT

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
    η-cns _ = ⟪ η ⟫ lt

    η-plc : (i : I) → ρ P (η-cns i)
    η-plc _ = ⟪ η ⟫↓ lt

    η-plc-contr : (i : I) → is-contr (ρ P (η-cns i))
    η-plc-contr i = equiv-preserves-level (⟪ η ⟫≃ ∘e (lower-equiv)⁻¹ ) Unit-is-contr

    η-dec-eqv : (i : I) (X : I → Type ℓ) → X i ≃ ⟦ P ⟧⟦ ⟪ η ⟫ lt ≺ X ⟧
    η-dec-eqv i X = ⟪ η ∣ X ⟫⇕-eqv ∘e lemma where
      lemma : {i : I} → X i ≃ ((p : ρ (IdP I) {i} lt) → X (τ (IdP I) {i} {lt} p))
      lemma {i} = equiv (λ x → cst x) (λ f → f lt) (λ f → λ= (λ x → idp)) (λ x → idp)

    η-τ= : ∀ {i} (p : ρ P (η-cns i)) → τ P p == i
    η-τ= {i} p = lemma₁ ∙ lemma₂

      where lemma : p == ⟪ η ⟫↓ lt
            lemma = contr-has-all-paths (η-plc-contr i) p (⟪ η ⟫↓ lt)

            lemma₁ : τ P p == τ P (⟪ η ⟫↓ lt)
            lemma₁ = ap (τ P) lemma
            
            lemma₂ : τ P (⟪ η ⟫↓ lt) == i
            lemma₂ = ! (⟪ η ⟫↓= lt)

    -- This can probably be done with things in the library.
    -- It's probably worth figuring out how to understand the
    -- library better.
    μ-inv : {i₀ i₁ : I} (c₀ : γ P i₀) (c₁ : γ P i₁)
            (δ₀ : ⟦ P ⟧⟦ c₀ ≺ γ P ⟧) (δ₁ : ⟦ P ⟧⟦ c₁ ≺ γ P ⟧)
            (p : i₀ == i₁) (q : c₀ == c₁ [ γ P ↓ p ])
            (r : δ₀ == δ₁ [ ⟦ P ⟧≺ (γ P) ↓ pair= p q ]) → 
            ⟪ μ ⟫ (c₀ , δ₀) == ⟪ μ ⟫ (c₁ , δ₁) [ γ P ↓ p ]
    μ-inv c₁ .c₁ δ₀ .δ₀ idp idp idp = idp
