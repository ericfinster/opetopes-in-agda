{-# OPTIONS --without-K #-}

open import HoTT

module Polynomial where

  record Poly {ℓ} (I : Type ℓ) (J : Type ℓ) : Type (lsucc ℓ) where
    field

      γ : (j : J) → Type ℓ
      ρ : {j : J} → (c : γ j) → Type ℓ
      τ : {j : J} → {c : γ j} → (p : ρ c) → I
  
  open Poly public

  ⟦_⟧⟦_≺_⟧ : ∀ {ℓ κ} {I J : Type ℓ} (P : Poly I J) → {j : J} → γ P j → (I → Type κ) → Type (lmax ℓ κ)
  ⟦ P ⟧⟦ c ≺ X ⟧ = Π (ρ P c) (X ∘ τ P) 

  ⟦_⟧≺ : ∀ {ℓ κ} {I J : Type ℓ} (P : Poly I J) (X : I → Type κ) → Σ J (γ P) → Type (lmax ℓ κ)
  ⟦ P ⟧≺ X (j , c) = ⟦ P ⟧⟦ c ≺ X ⟧

  ⟦_⟧ : ∀ {ℓ κ} {I J : Type ℓ} → Poly I J → (I → Type κ) → (J → Type (lmax ℓ κ))
  ⟦ P ⟧ X j = Σ (γ P j) (λ c → ⟦ P ⟧⟦ c ≺ X ⟧)  

  ⟦_↓_⟧≃ : ∀ {ℓ} {I J : Type ℓ} (P : Poly I J) 
           {j₀ j₁ : J} {q : j₀ == j₁} {c₀ : γ P j₀} {c₁ : γ P j₁}
           (r : c₀ == c₁ [ γ P ↓ q ]) → ρ P c₀ ≃ ρ P c₁
  ⟦_↓_⟧≃ P {q = idp} idp = ide _

  ρ-transp : ∀ {ℓ} {I J : Type ℓ} (P : Poly I J)
             {j₀ j₁ : J} {q : j₀ == j₁} {c₀ : γ P j₀} → 
             ρ P c₀ ≃ ρ P (transport (γ P) q c₀)
  ρ-transp P {q = idp} = ide _

  ⟦_↓_⟧↓ : ∀ {ℓ} {I J : Type ℓ} (P : Poly I J) 
          {j₀ j₁ : J} {q : j₀ == j₁} {c₀ : γ P j₀} {c₁ : γ P j₁} 
          (r : c₀ == c₁ [ γ P ↓ q ]) → ρ P c₀ → ρ P c₁
  ⟦ P ↓ r ⟧↓ p = –> ⟦ P ↓ r ⟧≃ p

  ⟦_↓_⟧↓= : ∀ {ℓ} {I J : Type ℓ} (P : Poly I J) 
           {j₀ j₁ : J} {q : j₀ == j₁} {c₀ : γ P j₀} {c₁ : γ P j₁} 
           (r : c₀ == c₁ [ γ P ↓ q ]) (p : ρ P c₀) → 
           τ P p == τ P (⟦ P ↓ r ⟧↓ p)
  ⟦_↓_⟧↓= P {q = idp} idp p = idp

  infixr 60 _⊗_
  infixr 50 _⊕_
  infixr 40 _⊚_

  _⊕_ : ∀ {ℓ} {I J : Type ℓ} → Poly I J → Poly I J → Poly I J
  γ (P ⊕ Q) j = γ P j ⊔ γ Q j
  ρ (P ⊕ Q) (inl c) = ρ P c
  ρ (P ⊕ Q) (inr c) = ρ Q c
  τ (P ⊕ Q) {c = inl c} p = τ P p
  τ (P ⊕ Q) {c = inr c} p = τ Q p

  _⊗_ : ∀ {ℓ} {I J : Type ℓ} → Poly I J → Poly I J → Poly I J
  γ (P ⊗ Q) j = γ P j × γ Q j
  ρ (P ⊗ Q) (cp , cq) = ρ P cp ⊔ ρ Q cq
  τ (P ⊗ Q) (inl p) = τ P p
  τ (P ⊗ Q) (inr p) = τ Q p

  _⊚_ : ∀ {ℓ} {I J K : Type ℓ} → Poly I J → Poly J K → Poly I K
  γ (P ⊚ Q) = ⟦ Q ⟧ (γ P)
  ρ (P ⊚ Q) (c , φ) = Σ (ρ Q c) (ρ P ∘ φ)
  τ (P ⊚ Q) (q , p) = τ P p

  _–_ : ∀ {ℓ} (I : Type ℓ) (i : I) → Type ℓ
  I – i = Σ I (λ i' → i ≠ i')

  ∂ : ∀ {ℓ} {I J : Type ℓ} → Poly I J → Poly I J
  γ (∂ P) j = Σ (γ P j) (ρ P)
  ρ (∂ P) (c , p) = ρ P c – p
  τ (∂ P) (p , _) = τ P p

  IdP : ∀ {ℓ} (I : Type ℓ) → Poly I I
  γ (IdP I) _ = Lift ⊤
  ρ (IdP I) _ = Lift ⊤
  τ (IdP I) {j} _ = j

