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
    η-dec-eqv i X = ⟪ η ∣ X ⟫⇕-eqv ∘e lemma

      where lemma : {i : I} → X i ≃ ((p : ρ (IdP I) {i} lt) → X (τ (IdP I) {i} {lt} p))
            lemma {i} = equiv (λ x → cst x) (λ f → f lt) (λ f → λ= (λ x → idp)) (λ x → idp)


