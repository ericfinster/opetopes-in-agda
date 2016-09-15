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

--    {-# TERMINATING #-}
--    fr-μ′ : FrP ⊚ FrP ⇝ FrP
--    γ-map fr-μ′ (leaf i , ψ) = ψ lt
--    γ-map fr-μ′ (node (c , φ) , ψ) = node (c , (λ p → γ-map fr-μ′ (φ p , (λ p′ → ψ (p , p′)))))
--    ρ-eqv fr-μ′ = {!!}
--    τ-coh fr-μ′ = {!!}

    -- Any polynomial with a "unit" and "multiplication" admits a map from FrP
    -- fr-univ : {Q : Poly I I} (η₀ : IdP I ⇝ Q) (μ₀ : Q ⊚ P ⇝ Q) → FrP ⇝ Q
    -- fr-univ {Q} η₀ μ₀ = ⊚-unit-l FrP ▶ (η₀ ∥ poly-id FrP) ▶ fr-fix μ₀

    open ADMIT

    fr-η-left-law : ⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ ≈ poly-id FrP
    fr-η-left-law (leaf i) = lcl-eqv idp (λ _ → idp) (λ _ → idp)
    fr-η-left-law (node (c , φ)) = lcl-eqv γ-eq ρ-eq ADMIT
       where IH : (p : ρ P c) → (⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ) ≈ (poly-id FrP) ⓐ φ p
             IH p = fr-η-left-law (φ p)

             γ-eq : ⟪ ⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ ⟫ (node (c , φ))
                    == ⟪ poly-id FrP ⟫ (node (c , φ))
             γ-eq = ↓-W-node-lcl-in (γ≈ ∘ IH)

             ρ-eq : (p : ρ FrP (node (c , φ))) →
                    (⟪ ⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ ⟫↓ p) ==
                    (⟪ poly-id FrP ⟫↓ p) [ ρ FrP ↓ γ-eq ]
             ρ-eq (p , l) = ↓-leaf-lcl-in (γ≈ ∘ IH) (ρ≈ (IH p) l)

--             τ-eq : (p : ρ FrP (node (c , φ))) →
--                    (⟪ ⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ ⟫↓= p) ==
--                    (⟪ poly-id FrP ⟫↓= p) [ (λ cp → (τ FrP p) == τ FrP (snd cp)) ↓ (pair= γ-eq (ρ-eq p)) ]
--             τ-eq (p , l) = {!!}

    -- -- The right law is definitional
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
    fr-μ-assoc-law (node (c , φ) , ψ) = lcl-eqv γ-eq {!!} ADMIT
      where γ-eq : ⟪ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫ (node (c , φ) , ψ) ==
                   ⟪ (fr-μ ∥ poly-id FrP) ▶ fr-μ ⟫ (node (c , φ) , ψ)
            γ-eq = γ≈ (unroll ((c , φ) , ψ)) ∙ ↓-W-node-lcl-in (λ p → γ≈ (fr-μ-assoc-law (φ p , λ p₁ → ψ (p , p₁))))

    FrM : PolyMonad I
    MP FrM = FrP
    η FrM = fr-η
    μ FrM = fr-μ

    η-left-law FrM = fr-η-left-law
    η-right-law FrM = fr-η-right-law
    μ-assoc-law FrM = ADMIT

    -- fr-fix-unit : {Q : Poly I I} (α : Q ⊚ P ⇝ Q) → (poly-id Q ∥ fr-η) ▶ fr-fix α ≈ ⊚-unit-inv-r Q
    -- fr-fix-unit {Q} α c = leq idp (λ p → idp) (λ p → idp)

    -- fr-fix-mult : {Q : Poly I I} (α : Q ⊚ P ⇝ Q) → (poly-id Q ∥ fr-P) ▶ fr-fix α ≈ ⊚-assoc-l Q FrP P ▶ (fr-fix α ∥ poly-id P) ▶ α
    -- fr-fix-mult {Q} α c = leq idp (λ p → idp ) lemma

    --   where lemma : (p : ρ (Q ⊚ FrP ⊚ P) c) →
    --                 ⟪ (poly-id Q ∥ fr-P) ▶ fr-fix α ⟫↓= p ==
    --                 ⟪ ⊚-assoc-l Q FrP P ▶ (fr-fix α ∥ poly-id P) ▶ α ⟫↓= p
    --         lemma ((p , l) , q) =
    --           ⟪ fr-fix α ⟫↓= (l , q) ∙ ⟪ α ⟫↓= (p , (⟪ fr-fix α ⟫↓ ((l , q))))
    --             =⟨ ! (∙-unit-r (⟪ fr-fix α ⟫↓= (l , q))) |in-ctx (λ x → x ∙ ⟪ α ⟫↓= (p , (⟪ fr-fix α ⟫↓ ((l , q))))) ⟩
    --           (⟪ fr-fix α ⟫↓= (l , q) ∙ idp) ∙ ⟪ α ⟫↓= (p , (⟪ fr-fix α ⟫↓ ((l , q))))
    --             =⟨ ! (ap-idf (⟪ fr-fix α ⟫↓= (l , q) ∙ idp)) |in-ctx (λ x → x ∙ ⟪ α ⟫↓= (p , (⟪ fr-fix α ⟫↓ ((l , q))))) ⟩
    --           ap (λ i → i) (⟪ fr-fix α ⟫↓= (l , q) ∙ idp) ∙ ⟪ α ⟫↓= (p , (⟪ fr-fix α ⟫↓ ((l , q)))) ∎

    -- fr-unique : {Q : Poly I I} {α β : FrP ⇝ Q} →
    --             fr-η ▶ α ≈ fr-η ▶ β →
    --             fr-P ▶ α ≈ fr-P ▶ β →
    --             α ≈ β
    -- fr-unique η-eq μ-eq (leaf i) = leq (γ≈ (η-eq lt)) (ρ≈ (η-eq lt)) (τ≈ (η-eq lt))
    -- fr-unique η-eq μ-eq (node (c , φ)) = leq (γ≈ (μ-eq (c , φ))) (ρ≈ (μ-eq (c , φ))) (τ≈ (μ-eq (c , φ)))

    -- Here is the identity which you seem to need to
    -- complete the proof.  It is the exact analog of the
    -- decoration lemma you had before.  I would still like
    -- to see this fit nicer into a general scheme ...

    -- fr-fix-mult : {Q : Poly I I} (α : Q ⊚ P ⇝ Q) → (poly-id Q ∥ fr-P) ▶ fr-fix α ≈ ⊚-assoc-l Q FrP P ▶ (fr-fix α ∥ poly-id P) ▶ α
    -- fr-fix-mult {Q} α c = leq idp (λ p → idp ) lemma


    -- COMPARE:
    -- (poly-id Q ∥ fr-P) ▶ fr-fix α ≈
    -- ⊚-assoc-l Q FrP P ▶ (fr-fix α ∥ poly-id P) ▶ α

    -- unroll : (poly-id (FrP ⊚ FrP) ∥ fr-P) ▶ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ≈
    --          ⊚-assoc-l (FrP ⊚ FrP) FrP P ▶ ((⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ) ∥ poly-id P) ▶ fr-P
    -- unroll = ADMIT

    -- {-# TERMINATING #-}
    -- fr-μ-assoc-law : ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ≈ (fr-μ ∥ poly-id FrP) ▶ fr-μ
    -- fr-μ-assoc-law (leaf i , ψ) = leq idp (λ p → idp) ADMIT
    -- fr-μ-assoc-law (node (c , φ) , ψ) = leq γ-eq ρ-eq ADMIT

    --   where γ-eq : ⟪ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫ (node (c , φ) , ψ) ==
    --                ⟪ (fr-μ ∥ poly-id FrP) ▶ fr-μ ⟫ (node (c , φ) , ψ)
    --         γ-eq = γ≈ (unroll ((c , φ) , ψ)) ∙ ↓-W-node-lcl-in (λ p → γ≈ (fr-μ-assoc-law (φ p , λ p₁ → ψ (p , p₁))))

    --         ρ-eq : (p : ρ ((FrP ⊚ FrP) ⊚ FrP) (node (c , φ) , ψ)) →
    --                ⟪ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫↓ p ==
    --                ⟪ (fr-μ ∥ poly-id FrP) ▶ fr-μ ⟫↓ p [ ρ FrP ↓ γ-eq ]
    --         ρ-eq p = ?

    --           -- where dec₀ : ⟦ P ⟧⟦ c ≺ γ FrP ⟧
    --           --       dec₀ p = ⟪ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫ (φ p , λ p₁ → ψ (p , p₁))

    --           --       dec₁ : ⟦ P ⟧⟦ c ≺ γ FrP ⟧
    --           --       dec₁ p = ⟪ (fr-μ ∥ poly-id FrP) ▶ fr-μ ⟫ (φ p , λ p₁ → ψ (p , p₁))

    --           --       IH : dec₀ == dec₁
    --           --       IH = λ= (λ p → γ≈ (fr-μ-assoc-law (φ p , λ p₁ → ψ (p , p₁))))

    --                 -- bleep : γ (FrP ⊚ P) _
    --                 -- bleep = ⟪ ⊚-assoc-l (FrP ⊚ FrP) FrP P ▶ ((⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ) ∥ poly-id P) ⟫ ((c , φ) , ψ)
    --                 -- -- (FrP ⊚ FrP) ⊚ (FrP ⊚ P) ⇝ ((FrP ⊚ FrP) ⊚ FrP) ⊚ P ⇝ (FrP ⊚ (FrP ⊚ FrP)) ⊚ P ⇝ (FrP ⊚ FrP) ⊚ P ⇝ FrP ⊚ P

    --                 -- blorp : γ (FrP ⊚ P) _
    --                 -- blorp = ⟪ ⊚-assoc-l (FrP ⊚ FrP) FrP P ▶ (((fr-μ ∥ poly-id FrP) ▶ fr-μ) ∥ poly-id P) ⟫ ((c , φ) , ψ)

    --                 -- fullIH : bleep == blorp
    --                 -- fullIH = pair= idp IH

    --               --   res₀ : ⟦ P ⟧⟦ c ≺ γ FrP ⟧
    --               --   res₀ p = ⟪ fr-μ ⟫ (⟪ fr-μ ⟫ (φ p , λ p₁ → fst (ψ (p , p₁))) ,
    --               --     (λ p₁ → ⟪ poly-id FrP ∣ fr-μ ⟫⇕ (λ pp → snd (ψ (fst pp)) (snd pp)) (p , p₁)))
    --               --     --(λ p₁ → ⟪ poly-id FrP ∣ fr-μ ⟫⇕ (snd (⟪ ⊚-assoc-r FrP FrP FrP ⟫ (node (c , φ) , ψ))) (p , p₁)))

    --               -- -- ⊚-assoc-r (c , φ) = (c , (λ p → fst (φ p))) , (λ pp → snd (φ (fst pp)) (snd pp))
    --               -- -- ⊚-assoc-l ((c , φ) , ψ) = (c , (λ p → (φ p , (λ q → ψ (p , q)))))
    --               -- -- (α ∥ β) (c , φ) = (⟪ β ⟫ c , ⟪ α ∣ β ⟫⇕ φ)
    --               -- -- (poly-id Q ∥ fr-P) ▶ fr-fix α ≈ ⊚-assoc-l Q FrP P ▶ (fr-fix α ∥ poly-id P) ▶ α

    --               --   res₁ : ⟦ P ⟧⟦ c ≺ γ FrP ⟧
    --               --   res₁ p = ⟪ fr-μ ⟫ (φ p , (λ p₁ → ⟪ fr-μ ∣ poly-id FrP ⟫⇕ ψ (p , p₁)))
    --               --   --dec₁ p = ⟪ (fr-μ ∥ poly-id FrP) ▶ fr-μ ⟫ (φ p , λ p₁ → ψ (p , p₁))

    --               --   finale : res₀ == res₁
    --               --   finale = {!γ≈ (unroll ((c , φ) , ψ))!}

    --               --   maybe : (p : ρ P c) → res₁ p == dec₁ p
    --               --   maybe p = idp
