{-# OPTIONS --without-K #-}

open import HoTT

module Simple where

  record Monad : Type₁ where
    field

      Idx : Type₀

      γ : Idx → Type₀
      ρ : {i : Idx} → (c : γ i) → Type₀
      τ : {i : Idx} → {c : γ i} → (p : ρ c) → Idx
      
      η : (i : Idx) → γ i
      μ : {i : Idx} → (c : γ i) → (δ : (p : ρ c) → γ (τ p)) → γ i

      ηp : (i : Idx) → ρ (η i)
      μp : {i : Idx} → {c : γ i} → {δ : (p : ρ c) → γ (τ p)} →
           (p : ρ c) → (q : ρ (δ p)) → ρ (μ c δ)

      ηp-unique : {i : Idx} → (p : ρ (η i)) → p == ηp i
      ηp-compat : {i : Idx} → τ (ηp i) == i
      μp-compat : {i : Idx} → {c : γ i} → {δ : (p : ρ c) → γ (τ p)} →
                  (p : ρ c) → (q : ρ (δ p)) → τ (μp {δ = δ} p q) == τ q

      unit-l : {i : Idx} → (c : γ i) → μ c (λ p → η (τ p)) == c
      unit-r : {i : Idx} → (δ : (p : ρ (η i)) → γ (τ p)) →
               δ (ηp i) == μ (η i) δ [ γ ↓ ηp-compat {i} ]

      assoc : {i : Idx} → (c : γ i) →
              (δ : (p : ρ c) → γ (τ p)) →
              (ε : (q : ρ (μ c δ)) → γ (τ q)) →
              μ (μ c δ) ε == μ c (λ p → μ (δ p) (λ q → transport γ (μp-compat {δ = δ} p q) (ε (μp {δ = δ} p q))))
              
  open Monad

  ⟦_⟧⟦_≺_⟧ : (M : Monad) → {i : Idx M} → (c : γ M i) → (X : Idx M → Type₀) → Type₀
  ⟦ M ⟧⟦ c ≺ X ⟧ = (p : ρ M c) → X (τ M p)

  ⟦_⟧ : (M : Monad) → (X : Idx M → Type₀) → Idx M → Type₀
  ⟦ M ⟧ X i = Σ (γ M i) (λ c → ⟦ M ⟧⟦ c ≺ X ⟧)
