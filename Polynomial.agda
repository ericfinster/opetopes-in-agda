{-# OPTIONS --without-K #-}

module Polynomial where

open import HoTT

record Poly {ℓ} (I : Type ℓ) (J : Type ℓ) : Type (lsucc ℓ) where
  constructor _≺_/_
  field
    γ : (j : J) → Type ℓ
    ρ : {j : J} → (c : γ j) → Type ℓ
    τ : {j : J} → {c : γ j} → (p : ρ c) → I

  ρ-Σ : Σ J γ → Type ℓ
  ρ-Σ = uncurryi ρ

  τ-Σ : Σ (Σ J γ) ρ-Σ → I
  τ-Σ (_ , p) = τ p

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

module _ {ℓ} {I : Type ℓ} (P : Poly I I) where
  τ-inv : {i i′ : I} {i=i′ : i == i′}
          {c : γ P i} {c′ : γ P i′} (c=c′ : c == c′ [ γ P ↓ i=i′ ])
          {p : ρ P c} {p′ : ρ P c′} (p=p′ : p == p′ [ ρ-Σ P ↓ pair= i=i′ c=c′ ])
          → τ P p == τ P p′
  τ-inv {i=i′ = idp} idp idp  = idp

  ↓-≺-in : ∀ {κ} {X : I → Type κ} {i i′ : I} {i=i′ : i == i′}
            {c : γ P i} {c′ : γ P i′}          {c=c′ : c == c′ [ γ P ↓ i=i′ ]}
            {φ : ⟦ P ⟧⟦ c ≺ X ⟧}{φ′ : ⟦ P ⟧⟦ c′ ≺ X ⟧}
            → ({p : ρ P c} {p′ : ρ P c′} (p=p′ : p == p′ [ ρ-Σ P ↓ pair= i=i′ c=c′ ])
               → φ p == φ′ p′ [ X ↓ τ-inv c=c′ p=p′ ])
            → φ == φ′ [ ⟦ P ⟧≺ X ↓ pair= i=i′ c=c′ ]
  ↓-≺-in {i=i′ = idp} {c=c′ = idp} f = λ= (λ p → f idp)

  ↓-≺-out : ∀ {κ} {X : I → Type κ} {i i′ : I}         {i=i′ : i == i′}
            {c : γ P i} {c′ : γ P i′}                   {c=c′ : c == c′ [ γ P ↓ i=i′ ]}
            {φ : ⟦ P ⟧⟦ c ≺ X ⟧} {φ′ : ⟦ P ⟧⟦ c′ ≺ X ⟧} (φ=φ′ : φ == φ′ [ ⟦ P ⟧≺ X ↓ pair= i=i′ c=c′ ])
            → ({p : ρ P c} {p′ : ρ P c′} (p=p′ : p == p′ [ ρ-Σ P ↓ pair= i=i′ c=c′ ])
                → φ p == φ′ p′ [ X ↓ τ-inv c=c′ p=p′ ])
  ↓-≺-out {i=i′ = idp} {c=c′ = idp} q idp = app= q _

  ↓-≺-β : ∀ {κ} {X : I → Type κ} {i i′ : I} {i=i′ : i == i′}
           {c : γ P i} {c′ : γ P i′} {c=c′ : c == c′ [ γ P ↓ i=i′ ]}
           {φ : ⟦ P ⟧⟦ c ≺ X ⟧}{φ′ : ⟦ P ⟧⟦ c′ ≺ X ⟧}
           → (f : {p : ρ P c} {p′ : ρ P c′} (p=p′ : p == p′ [ ρ-Σ P ↓ pair= i=i′ c=c′ ])
              → φ p == φ′ p′ [ X ↓ τ-inv c=c′ p=p′ ])
           → {p : ρ P c} {p′ : ρ P c′} (p=p′ : p == p′ [ ρ-Σ P ↓ pair= i=i′ c=c′ ])
           → ↓-≺-out (↓-≺-in f) p=p′ == f p=p′
  ↓-≺-β {i=i′ = idp} {c=c′ = idp} f idp = app=-β (λ p → f idp) _

  -- not sure why we need {X = X} and {i=i′ = i=i′}
  ↓-≺-η : ∀ {κ} {X : I → Type κ} {i i′ : I} {i=i′ : i == i′}
          {c : γ P i} {c′ : γ P i′}                   {c=c′ : c == c′ [ γ P ↓ i=i′ ]}
          {φ : ⟦ P ⟧⟦ c ≺ X ⟧} {φ′ : ⟦ P ⟧⟦ c′ ≺ X ⟧} (φ=φ′ : φ == φ′ [ ⟦ P ⟧≺ X ↓ pair= i=i′ c=c′ ])
          → ↓-≺-in (↓-≺-out {X = X} {i=i′ = i=i′} φ=φ′) == φ=φ′
  ↓-≺-η {i=i′ = idp} {c=c′ = idp} q = ! (λ=-η q)

module _ {ℓ κ} {I J : Type ℓ} (P : Poly I J) {X : I → Type κ} where
  □ : ∀ {ℓ′} → (Σ I X → Type ℓ′) → (Σ J (⟦ P ⟧ X) → Type _)
  □ f (_ , _ , φ) = ∀ p → f (_ , φ p)

  ⋄ : ∀ {ℓ′} → (Σ I X → Type ℓ′) → (Σ J (⟦ P ⟧ X) → Type _)
  ⋄ f (_ , _ , φ) = Σ _ λ p → f (_ , φ p)
