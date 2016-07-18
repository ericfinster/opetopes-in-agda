{-# OPTIONS --without-K #-}

open import HoTT

open import opetopes.Polynomial
open import opetopes.CartesianMorphism
open import opetopes.PolynomialMonad
open import opetopes.PolyMisc

module opetopes.PullbackMonad where

  module _ {ℓ} {I : Set ℓ} (X : I → Set ℓ) (M : PolyMonad I) where
  
    open PolyMonad 

    T : Set ℓ
    T = Σ I X

    PbP : Poly T T
    γ PbP (i , x) = ⟦ P M ⟧ X i
    ρ PbP (c , φ) = ρ (P M) c
    τ PbP {c = c , φ} p = τ (P M) p , φ p

    π-pb : ⟦ fst ∣ fst ⟧⟦ PbP ⇒ (P M) ⟧
    γ-map π-pb (c , φ) = c
    ρ-eqv π-pb = ide _
    τ-coh π-pb p = idp

    -- pb-η : IdP T ⇝ PbP
    -- γ-map pb-η {j = i , x} _ = (⟪ η M ⟫ lt , ⟪ η M ∣ X ⟫⇓ (cst x))
    -- ρ-eqv pb-η = ⟪ η M ⟫≃
    -- τ-coh pb-η {j = i , x} p = pair= (⟪ η M ⟫↓= lt) (⟪ η M ∣ X ⟫⇓-coh (cst x) lt)

    -- pb-μ : PbP ⊚ PbP ⇝ PbP
    -- γ-map pb-μ ((c , φ) , ψ) = (⟪ μ M ⟫ (c , fst ∘ ψ) , ⟪ μ M ∣ X ⟫⇓ (λ { (p₀ , p₁) → snd (ψ p₀) p₁ }))
    -- ρ-eqv pb-μ {c = (c , φ) , ψ} = ⟪ μ M ⟫≃
    -- τ-coh pb-μ {c = (c , φ) , ψ} (p₀ , p₁) = pair= (⟪ μ M ⟫↓= (p₀ , p₁)) (⟪ μ M ∣ X ⟫⇓-coh (λ { (p₀ , p₁) → snd (ψ p₀) p₁ }) (p₀ , p₁))

    -- open ADMIT

    -- pb-η-left-law : ⊚-unit-l PbP ▶ (pb-η ∥ poly-id PbP) ▶ pb-μ ≈ poly-id PbP
    -- pb-η-left-law = ADMIT

    -- pb-η-right-law : ⊚-unit-r PbP ▶ (poly-id PbP ∥ pb-η) ▶ pb-μ ≈ poly-id PbP
    -- pb-η-right-law = ADMIT

    -- pb-μ-assoc-law : ⊚-assoc-r PbP PbP PbP ▶ (poly-id PbP ∥ pb-μ) ▶ pb-μ ≈ (pb-μ ∥ poly-id PbP) ▶ pb-μ
    -- pb-μ-assoc-law = ADMIT

    -- PbM : PolyMonad T 
    -- P PbM = PbP
    -- η PbM = pb-η
    -- μ PbM = pb-μ
    -- η-left-law PbM = pb-η-left-law
    -- η-right-law PbM = pb-η-right-law
    -- μ-assoc-law PbM = pb-μ-assoc-law

  -- -- Using the pullback, we can define maps of monads over a given fibration
  -- PolyMapOver : ∀ {ℓ} {I : Type ℓ} (X : I → Type ℓ) (M : PolyMonad (Σ I X)) (N : PolyMonad I) → Type ℓ 
  -- PolyMapOver X M N = PolyMonadMap M (PbM X N)


