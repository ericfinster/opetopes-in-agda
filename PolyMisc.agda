{-# OPTIONS --without-K #-}

open import HoTT

open import Polynomial
open import CartesianMorphism

module PolyMisc where

  --
  --  These lemmas come from Equivalences.agda, but we need them
  --  for the unit type lifted to a higher universe level
  --

  LUnit : ∀ {k} → Type k
  LUnit {k} = Lift {lzero} {k} Unit

  lt : ∀ {k} → LUnit {k}
  lt = lift unit

  module _ {j k} {B : LUnit {k} → Type j} where
    Σ₁-LUnit : Σ LUnit B ≃ B (lt)
    Σ₁-LUnit = equiv (λ {(lift unit , b) → b}) (λ b → (lt , b)) (λ _ → idp) (λ _ → idp)

    Π₁-LUnit : Π LUnit B ≃ B (lt)
    Π₁-LUnit = equiv (λ f → f lt) (λ b _ → b) (λ _ → idp) (λ _ → idp)

  module _ {i k} {A : Type i} where
    Σ₂-LUnit : Σ A (λ _ → LUnit {k}) ≃ A
    Σ₂-LUnit = equiv fst (λ a → (a , lt)) (λ _ → idp) (λ _ → idp)

    Π₂-LUnit : Π A (λ _ → LUnit {k}) ≃ LUnit {k}
    Π₂-LUnit = equiv (λ _ → lt) (λ _ _ → lt) (λ _ → idp) (λ _ → idp)

  --
  --  Now we can define some useful cartesian morphisms
  --

  -- Unicity maps
  ⊚-unit-l : ∀ {ℓ} {I : Type ℓ} (P : Poly I I) → P ⇝ IdP I ⊚ P
  γ-map (⊚-unit-l P) c = c , (λ x → lift tt)
  ρ-eqv (⊚-unit-l P) = (Σ₂-LUnit)⁻¹
  τ-coh (⊚-unit-l P) p = idp 

  ⊚-unit-inv-l : ∀ {ℓ} {I : Type ℓ} (P : Poly I I) → IdP I ⊚ P ⇝ P
  γ-map (⊚-unit-inv-l P) (c , φ) = c
  ρ-eqv (⊚-unit-inv-l P) = Σ₂-LUnit
  τ-coh (⊚-unit-inv-l P) p = idp

  ⊚-unit-r : ∀ {ℓ} {I : Type ℓ} (P : Poly I I) → P ⇝ P ⊚ IdP I
  γ-map (⊚-unit-r P) c = lt , cst c
  ρ-eqv (⊚-unit-r P) = (Σ₁-LUnit)⁻¹
  τ-coh (⊚-unit-r P) p = idp

  ⊚-unit-inv-r : ∀ {ℓ} {I : Type ℓ} (P : Poly I I) → P ⊚ IdP I  ⇝ P
  γ-map (⊚-unit-inv-r P) (lt , φ) = φ lt
  ρ-eqv (⊚-unit-inv-r P) = Σ₁-LUnit
  τ-coh (⊚-unit-inv-r P) p = idp

  -- Associativity of polynomial composition
  module _ {ℓ} {I J K L : Type ℓ} (P : Poly I J) (Q : Poly J K) (R : Poly K L) where

    ⊚-assoc-r : (P ⊚ Q) ⊚ R ⇝ P ⊚ (Q ⊚ R) 
    γ-map ⊚-assoc-r (c , φ) = (c , fst ∘ φ) , (λ { (p₀ , p₁) → snd (φ p₀) p₁ })
    ρ-eqv ⊚-assoc-r {c = c , φ} = (Σ-assoc)⁻¹
    τ-coh ⊚-assoc-r {c = c , φ} (p , (l₀ , l₁)) = idp

    ⊚-assoc-l : P ⊚ (Q ⊚ R) ⇝ (P ⊚ Q) ⊚ R 
    γ-map ⊚-assoc-l ((c , φ) , ψ) = (c , λ p → (φ p , λ q → ψ (p , q)))
    ρ-eqv ⊚-assoc-l {c = (c , φ) , ψ} = Σ-assoc
    τ-coh ⊚-assoc-l {c = (c , φ) , ψ} p = idp

  module _ {ℓ} {I J K : Type ℓ} (P : Poly I J) (Q R : Poly J K) where

    ⊚-dist-⊕ : P ⊚ (Q ⊕ R) ⇝ (P ⊚ Q) ⊕ (P ⊚ R)
    γ-map ⊚-dist-⊕ (inl cq , φ) = inl (cq , φ)
    γ-map ⊚-dist-⊕ (inr cr , φ) = inr (cr , φ)
    ρ-eqv ⊚-dist-⊕ {c = inl cq , φ} = ide _
    ρ-eqv ⊚-dist-⊕ {c = inr cr , φ} = ide _
    τ-coh ⊚-dist-⊕ {c = inl cq , φ} p = idp
    τ-coh ⊚-dist-⊕ {c = inr cr , φ} p = idp

