{-# OPTIONS --without-K #-}

open import HoTT

open import Polynomial
open import PolyMisc
open import PolynomialMonad
open import CartesianMorphism
open import WTypes

module FreeMonad where

  module _ {ℓ} {I : Set ℓ} (P : Poly I I) where

    open PolyMonad renaming (P to MP)

    FrP : Poly I I
    γ FrP = W P
    ρ FrP = leafOf
    τ FrP = leafType

    fr-η : IdP I ⇝ FrP
    γ-map fr-η {i} lt = leaf i
    ρ-eqv fr-η = ide _
    τ-coh fr-η p = idp

    fr-Η : P ⇝ FrP
    γ-map fr-Η = corolla
    ρ-eqv fr-Η = (Σ₂-LUnit)⁻¹
    τ-coh fr-Η p = idp

    fr-P : FrP ⊚ P ⇝ FrP
    γ-map fr-P (c , φ) = node (c , φ)
    ρ-eqv fr-P {j} {c , φ} = ide _
    τ-coh fr-P p = idp

    {-# TERMINATING #-}
    fr-fix : {Q : Poly I I} (α : Q ⊚ P ⇝ Q) → Q ⊚ FrP ⇝ Q
    γ-map (fr-fix α) (leaf i , ψ) = ψ lt
    γ-map (fr-fix α) (node (c , φ) , ψ) = ⟪ α ⟫ (c , (λ p₀ → γ-map (fr-fix α) (φ p₀ , (λ p₁ → ψ (p₀ , p₁)))))
    ρ-eqv (fr-fix α) {c = leaf ._ , ψ} = Σ₁-LUnit
    ρ-eqv (fr-fix α) {c = node (c , φ) , ψ} = ⟪ α ⟫≃ ∘e equiv-Σ-snd (λ p → ρ-eqv (fr-fix α)) ∘e Σ-assoc
    τ-coh (fr-fix α) {c = leaf ._ , ψ} p = idp
    τ-coh (fr-fix α) {c = node (c , φ) , ψ} ((p , l) , q) = τ-coh (fr-fix α) (l , q) ∙ ⟪ α ⟫↓= (p , –> (ρ-eqv (fr-fix α)) (l , q))

    fr-μ : FrP ⊚ FrP ⇝ FrP
    fr-μ = fr-fix fr-P

    -- Any polynomial with a "unit" and "multiplication" admits a map from FrP
    -- fr-univ : {Q : Poly I I} (η₀ : IdP I ⇝ Q) (μ₀ : Q ⊚ P ⇝ Q) → FrP ⇝ Q
    -- fr-univ {Q} η₀ μ₀ = ⊚-unit-l FrP ▶ (η₀ ∥ poly-id FrP) ▶ fr-fix μ₀

    open ADMIT

    fr-η-left-law : ⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ ≈ poly-id FrP
    fr-η-left-law (leaf i) = lcl-eqv idp (λ _ → idp) (λ _ → idp)
    fr-η-left-law (node (c , φ)) = lcl-eqv γ-eq ρ-eq ADMIT
       where IH : (p : ρ P c) → (⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ) ≈ (poly-id FrP) ⓐ φ p
             IH p = fr-η-left-law (φ p)

             γ-eq : ⟪ ⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ ⟫ (node (c , φ)) ==
                    ⟪ poly-id FrP ⟫ (node (c , φ))
             γ-eq = ↓-W-node-lcl-in (γ≈ ∘ IH)

             ρ-eq : (p : ρ FrP (node (c , φ))) →
                    (⟪ ⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ ⟫↓ p) ==
                    (⟪ poly-id FrP ⟫↓ p) [ ρ FrP ↓ γ-eq ]
             ρ-eq (p , l) = ↓-leaf-lcl-in (γ≈ ∘ IH) (ρ≈ (IH p) l)

--             τ-eq : (p : ρ FrP (node (c , φ))) →
--                    (⟪ ⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ ⟫↓= p) ==
--                    (⟪ poly-id FrP ⟫↓= p) [ (λ cp → (τ FrP p) == τ FrP (snd cp)) ↓ (pair= γ-eq (ρ-eq p)) ]
--             τ-eq (p , l) = {!!}

    fr-η-right-law : ⊚-unit-r FrP ▶ (poly-id FrP ∥ fr-η) ▶ fr-μ ≈ poly-id FrP
    γ≈ (fr-η-right-law c) = idp
    ρ≈ (fr-η-right-law c) p = idp
    τ≈ (fr-η-right-law c) p = idp

    unroll : (poly-id (FrP ⊚ FrP) ∥ fr-P) ▶ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ≈
             ⊚-assoc-l (FrP ⊚ FrP) FrP P ▶ ((⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ) ∥ poly-id P) ▶ fr-P
    unroll = ADMIT

    {-# TERMINATING #-}
    fr-μ-assoc-law : ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ≈ (fr-μ ∥ poly-id FrP) ▶ fr-μ
    fr-μ-assoc-law (leaf i , ψ) = lcl-eqv idp (λ p → idp) ADMIT
    fr-μ-assoc-law (node (c , φ) , ψ) = lcl-eqv γ-eq ρ-eq ADMIT
      where γ-eq : ⟪ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫ (node (c , φ) , ψ) ==
                   ⟪ (fr-μ ∥ poly-id FrP) ▶ fr-μ ⟫ (node (c , φ) , ψ)
            --γ-eq = γ≈ (unroll ((c , φ) , ψ)) ∙ ↓-W-node-lcl-in (λ p → γ≈ (fr-μ-assoc-law (φ p , λ p₁ → ψ (p , p₁))))
            γ-eq =
              ⟪ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫ (node (c , φ) , ψ)
                =⟨ idp ⟩
              ⟪ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫ (⟪ ⊚-assoc-r FrP FrP FrP ⟫ (node (c , φ) , ψ))
                =⟨ idp ⟩
              ⟪ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫ ((node (c , φ) , (λ x → fst (ψ x))) , (λ w → snd (ψ (fst w)) (snd w)))
                =⟨ idp ⟩
              ⟪ fr-μ ⟫ ( ⟪ poly-id FrP ∥ fr-μ ⟫ ((node (c , φ) , (λ x → fst (ψ x))) , (λ w → snd (ψ (fst w)) (snd w))))
--                =⟨ idp ⟩
--              node (c ,
--                (λ p₀ →
--                  γ-map (fr-fix fr-P)
--                    ((γ-map fr-μ (φ p₀ , (λ p₁ → fst (ψ (p₀ , p₁))))) ,
--                     (λ p₁ → coe
--                       (ap (W P)
--                         ((τ-coh fr-μ (<– (ρ-eqv fr-μ) p₁)) ∙
--                           ap (leafType ∘ snd)
--                             (! (ap (λ x → fst x , –> (ρ-eqv fr-μ) (<– (ρ-eqv fr-μ) (snd x)))
--                               (ap (_,_ p₀) (<–-inv-r (ρ-eqv fr-μ) p₁))) ∙
--                             ap (λ ab → fst ab , –> (ρ-eqv fr-μ) (snd ab))
--                               (ap (_,_ p₀) (<–-inv-r (ρ-eqv fr-μ) (<– (ρ-eqv fr-μ) p₁))) ∙
--                             ap (_,_ p₀)
--                               (<–-inv-r (ρ-eqv fr-μ) p₁))))
--                       (snd (ψ (p₀ , fst (<– (ρ-eqv fr-μ) p₁))) (snd (<– (ρ-eqv fr-μ) p₁)))))))
                =⟨ ADMIT ⟩
              node (c , (λ p → γ-map (fr-fix fr-P) (φ p , (λ p′ → γ-map (fr-fix fr-P) (ψ (p , p′))))))
                =⟨ idp ⟩
              ⟪ (fr-μ ∥ poly-id FrP) ▶ fr-μ ⟫ (node (c , φ) , ψ) ∎
                where
                  flant : (p : ρ P c) → γ-map fr-μ (φ p , λ p′ → fst (ψ (p , p′))) == φ p
                  flant p = ADMIT

            dec : ⟦ P ⟧⟦ c ≺ γ FrP ⟧
            dec p = ⟪ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫ (φ p , λ p′ → ψ (p , p′))

            dec′ : ⟦ P ⟧⟦ c ≺ γ FrP ⟧
            dec′ p = ⟪ (fr-μ ∥ poly-id FrP) ▶ fr-μ ⟫ (φ p , λ p′ → ψ (p , p′))

            IH : (p : ρ P c) → dec p == dec′ p
            IH p = γ≈ (fr-μ-assoc-law (φ p , λ p′ → ψ (p , p′)))

            ρ-eq : (p : Σ (Σ (ρ P c) (λ q → leafOf (φ q))) ((λ w → Σ (leafOf (fst w)) (leafOf ∘ snd w)) ∘ ψ))
                → ⟪ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫↓ p ==
                   ⟪ (fr-μ ∥ poly-id FrP) ▶ fr-μ ⟫↓ p
                   [ leafOf ↓ γ-eq ]
            ρ-eq p = ADMIT


    FrM : PolyMonad I
    MP FrM = FrP
    η FrM = fr-η
    μ FrM = fr-μ

    η-left-law FrM = fr-η-left-law
    η-right-law FrM = fr-η-right-law
    μ-assoc-law FrM = ADMIT
