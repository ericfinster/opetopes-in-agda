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
