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

    po-inv : ∀ {ℓ} {X : Type ℓ} {P : X → Type ℓ}
             {x₀ : X} {x₁ : X} (p : x₀ == x₁)
             {a₀ : P x₀} {a₁ : P x₀}
             (q : a₀ == a₁ [ P ↓ p ∙ (! p) ]) → a₀ == a₁
    po-inv idp idp = idp             

    η-dec-unique : {i₀ i₁ : I} (p : i₀ == i₁)
                   (δ₀ : ⟦ P ⟧⟦ ⟪ η ⟫ {j = i₀} lt ≺ γ P ⟧) 
                   (δ₁ : ⟦ P ⟧⟦ ⟪ η ⟫ {j = i₁} lt ≺ γ P ⟧) 
                   (q : δ₀ (⟪ η ⟫↓ lt) == δ₁ (⟪ η ⟫↓ lt) [ γ P ↓ ap (λ j → τ P (⟪ η ⟫↓ {j = j} lt)) p ])
                   → δ₀ == δ₁ [ ⟦ P ⟧≺ (γ P) ↓ pair= p (apd (λ x → ⟪ η ⟫ {j = x} lt) p) ]
    η-dec-unique {i} {.i} idp δ₀ δ₁ q = λ= lemma

      where lemma : (p : ρ P (⟪ η ⟫ {i} lt)) → δ₀ p == δ₁ p
            lemma p = lem

              where α : p == ⟪ η ⟫↓ lt
                    α = contr-has-all-paths (η-plc-contr i) p (⟪ η ⟫↓ lt)

                    δ₀-over : δ₀ p == δ₀ (⟪ η ⟫↓ lt) [ (γ P) ∘ (τ P) ↓ α ]
                    δ₀-over = apd δ₀ α

                    δ₁-over : δ₁ (⟪ η ⟫↓ lt) == δ₁ p [ (γ P) ∘ (τ P) ↓ (! α) ]
                    δ₁-over = apd δ₁ (! α)

                    total-po : δ₀ p == δ₁ p [ (γ P) ∘ (τ P) ↓ α ∙ (! α) ]
                    total-po = δ₀-over ∙ᵈ q ∙ᵈ δ₁-over

                    lem : δ₀ p == δ₁ p
                    lem = po-inv α {δ₀ p} {δ₁ p} total-po
