{-# OPTIONS --without-K #-}
--{-# OPTIONS --show-implicit #-}

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
    τ-coh (fr-fix α) {c = node (c , φ) , ψ} ((p , l) , q) = ⟪ fr-fix α ⟫↓= (l , q) ∙ ⟪ α ⟫↓= (p , –> (ρ-eqv (fr-fix α)) (l , q))

    fr-μ : FrP ⊚ FrP ⇝ FrP
    fr-μ = fr-fix fr-P

    -- Any polynomial with a "unit" and "multiplication" admits a map from FrP
    -- fr-univ : {Q : Poly I I} (η₀ : IdP I ⇝ Q) (μ₀ : Q ⊚ P ⇝ Q) → FrP ⇝ Q
    -- fr-univ {Q} η₀ μ₀ = ⊚-unit-l FrP ▶ (η₀ ∥ poly-id FrP) ▶ fr-fix μ₀

    open ADMIT

    fr-η-left-law : ⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ ≈ poly-id FrP
    fr-η-left-law (leaf i) = lcl-eqv idp (λ _ → idp) (λ _ → idp)
    fr-η-left-law (node (c , φ)) = lcl-eqv γ-eq ρ-eq ADMIT where
      IH : (p : ρ P c) → (⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ) ≈ (poly-id FrP) ⓐ φ p
      IH p = fr-η-left-law (φ p)

      γ-eq : ⟪ ⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ ⟫ (node (c , φ)) ==
             ⟪ poly-id FrP ⟫ (node (c , φ))
      γ-eq = ↓-W-node-lcl-in (γ≈ ∘ IH)

      ρ-eq : (p : ρ FrP (node (c , φ))) →
             (⟪ ⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ ⟫↓ p) ==
             (⟪ poly-id FrP ⟫↓ p) [ ρ FrP ↓ γ-eq ]
      ρ-eq (p , l) = ADMIT -- ↓-leaf-lcl-in (γ≈ ∘ IH) (ρ≈ (IH p) l)

--      τ-eq : (p : ρ FrP (node (c , φ))) →
--             (⟪ ⊚-unit-l FrP ▶ (fr-η ∥ poly-id FrP) ▶ fr-μ ⟫↓= p) ==
--             (⟪ poly-id FrP ⟫↓= p) [ (λ cp → (τ FrP p) == τ FrP (snd cp)) ↓ (pair= γ-eq (ρ-eq p)) ]
--      τ-eq (p , l) = {!!}

    fr-η-right-law : ⊚-unit-r FrP ▶ (poly-id FrP ∥ fr-η) ▶ fr-μ ≈ poly-id FrP
    γ≈ (fr-η-right-law c) = idp
    ρ≈ (fr-η-right-law c) p = idp
    τ≈ (fr-η-right-law c) p = idp

    --unroll : (poly-id (FrP ⊚ FrP) ∥ fr-P) ▶ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ≈
    --         ⊚-assoc-l (FrP ⊚ FrP) FrP P ▶ ((⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ) ∥ poly-id P) ▶ fr-P
    --unroll = ADMIT

    {-# TERMINATING #-}
    fr-μ-assoc-law : ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ≈ (fr-μ ∥ poly-id FrP) ▶ fr-μ
    fr-μ-assoc-law (leaf i , ψ) = lcl-eqv idp (λ p → idp) ADMIT
    fr-μ-assoc-law (node {i} (c , φ) , ψ) = lcl-eqv γ-eq ADMIT ADMIT where
      --c1 : (p : ρ P c) → ⟦ FrP ⟧ {!W {I = I}!} (τ P p)
      --c1 p = φ p , λ p′ → ψ (p , p′)

      dec : ⟦ P ⟧⟦ c ≺ γ FrP ⟧
      dec p = ⟪ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫ (φ p , λ p' → ψ (p , p'))

      dec′ : ⟦ P ⟧⟦ c ≺ γ FrP ⟧
      dec′ p = ⟪ (fr-μ ∥ poly-id FrP) ▶ fr-μ ⟫ (φ p , λ p' → ψ (p , p'))

      IH : (p : ρ P c) → dec p == dec′ p
      IH p = γ≈ (fr-μ-assoc-law (φ p , λ p' → ψ (p , p')))

      γ-eq : ⟪ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫ (node (c , φ) , ψ) ==
             ⟪ (fr-μ ∥ poly-id FrP) ▶ fr-μ ⟫ (node (c , φ) , ψ)
      γ-eq =
        ⟪ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫ (node (c , φ) , ψ)
          =⟨ idp ⟩
        ⟪ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫ ⊚-assoc-app
          =⟨ idp ⟩
        ⟪ fr-μ ⟫ (⟪ (poly-id FrP ∥ fr-μ) ⟫ ((c0) , λ w → snd (ψ (fst w)) (snd w)))
          =⟨ λ= lemma |in-ctx (λ x → node (c , (λ p → ⟪ fr-μ ⟫ (⟪ fr-μ ⟫ (φ p , (λ p′ → fst (ψ (p , p′)))) , x p)))) ⟩
        node (c , (λ p → ⟪ fr-μ ⟫ (⟪ fr-μ ⟫ (φ p , (λ p′ → fst (ψ (p , p′))))
                                              , ⟪ poly-id FrP ∣ fr-μ ⟫⇕ (λ x → snd (ψ (p , fst x)) (snd x)))))
          =⟨ ↓-W-node-lcl-in IH ⟩
        node (c , (λ p → ⟪ fr-μ ⟫ (φ p , (λ p′ → ⟪ fr-μ ⟫ (ψ (p , p′))))))
          =⟨ idp ⟩
        ⟪ fr-μ ⟫ (⟪ (fr-μ ∥ poly-id FrP) ⟫ (node (c , φ) , ψ))
          =⟨ idp ⟩
        ⟪ (fr-μ ∥ poly-id FrP) ▶ fr-μ ⟫ (node (c , φ) , ψ) ∎ where
          ⊚-assoc-app : ⟦ FrP ⊚ FrP ⟧ (W P) i
          ⊚-assoc-app = ⟪ ⊚-assoc-r FrP FrP FrP ⟫ (node (c , φ) , ψ)

          c0 : ⟦ FrP ⟧ (W P) i
          c0 = node (c , φ) , fst ∘ ψ

          c1 : (p : ρ P c) → ⟦ FrP ⟧ (W P) (τ P p)
          c1 p = φ p , λ p' → fst (ψ (p , p'))

          mul-dec : ⟦ P ⟧⟦ c ≺ W P ⟧
          mul-dec p = ⟪ fr-μ ⟫ (c1 p)

          ψ-copy : ⟦ FrP ⟧⟦ node (c , φ) ≺ ⟦ FrP ⟧ (W P) ⟧
          ψ-copy = ψ

          φ1 : ⟦ FrP ⊚ FrP ⟧⟦ c0 ≺ W P ⟧
          φ1 w = snd (ψ (fst w)) (snd w)

          φ2-of : (p : ρ P c) → ⟦ FrP ⊚ FrP ⟧⟦ c1 p ≺ W P ⟧
          φ2-of p w = snd (ψ (p , fst w)) (snd w)

          goal : (p : ρ P c) (l : leafOf (mul-dec p))
              → ⟪ poly-id FrP ∣ fr-μ ⟫⇕ φ1 (p , l)
                 == ⟪ poly-id FrP ∣ fr-μ ⟫⇕ (φ2-of p) l
          goal p l =
            ⟪ poly-id FrP ∣ fr-μ ⟫⇕ φ1 p,l
              =⟨ idp ⟩
            push fr-μ (W P) (W P) ⟪ poly-id FrP ⟫ φ1 p,l
              =⟨ idp ⟩
            transport (W P) p,l↑= (φ1 (⟪ fr-μ ⟫↑ p,l))
              =⟨ trans-∙ (⟪ fr-μ ⟫↓= (⟪ fr-μ ⟫↑ {c = c0} p,l)) (ap (τ FrP) (⟪ fr-μ ⟫⇅ {c = c0} p,l)) (φ1 (⟪ fr-μ ⟫↑ p,l)) ⟩
            transport (W P)
                      (ap (τ FrP) (⟪ fr-μ ⟫⇅ {c = c0} p,l))
                      (transport (W P) (⟪ fr-μ ⟫↓= (⟪ fr-μ ⟫↑ {c = c0} p,l)) (φ1 (⟪ fr-μ ⟫↑ p,l)))
              =⟨ idp ⟩
            transport (W P)
                      (ap (τ FrP) (⟪ fr-μ ⟫⇅ {c = c0} p,l))
                      (transport (W P) (⟪ fr-μ ⟫↓= (⟪ fr-μ ⟫↑ {c = c0} p,l)) (φ2-of p (⟪ fr-μ ⟫↑ l)))
              =⟨ {!fst ∘ ψ !} ⟩
            transport (W P) (ap (τ FrP) (⟪ fr-μ ⟫⇅ {c = c1 p} l)) (transport (W P) (⟪ fr-μ ⟫↓= (⟪ fr-μ ⟫↑ {c = c1 p} l)) (φ2-of p (⟪ fr-μ ⟫↑ l)))
              =⟨ ! (trans-∙ (⟪ fr-μ ⟫↓= (⟪ fr-μ ⟫↑ {c = c1 p} l)) (ap (τ FrP) (⟪ fr-μ ⟫⇅ {c = c1 p} l)) (φ2-of p (⟪ fr-μ ⟫↑ l))) ⟩
            transport (W P) l↑= (φ2-of p (⟪ fr-μ ⟫↑ l))
              =⟨ idp ⟩
            push fr-μ (W P) (W P) ⟪ poly-id FrP ⟫ (φ2-of p) l
              =⟨ idp ⟩
            ⟪ poly-id FrP ∣ fr-μ ⟫⇕ (φ2-of p) l ∎ where
              p,l : leafOf (⟪ fr-μ ⟫ (c0))
              p,l = p , l

              p,l↑= : leafType (snd (⟪ fr-μ ⟫↑ {c = c0} p,l))
                      == leafType l
              p,l↑= = ⟪ fr-μ ⟫↓= (⟪ fr-μ ⟫↑ {c = c0} p,l)
                      ∙ ap (τ FrP) (⟪ fr-μ ⟫⇅ {c = c0} p,l)

              l↑= : leafType (snd (⟪ fr-μ ⟫↑ {c = c1 p} l)) == leafType l
              l↑= = ⟪ fr-μ ⟫↓= (⟪ fr-μ ⟫↑ {c = c1 p} l)
                    ∙ ap (τ FrP) (⟪ fr-μ ⟫⇅ {c = c1 p} l)

              isthistrue : (transport (W P) (⟪ fr-μ ⟫↓= (⟪ fr-μ ⟫↑ {c = c0} p,l)) (φ2-of p (⟪ fr-μ ⟫↑ l)))
                           == (transport (W P) (⟪ fr-μ ⟫↓= (⟪ fr-μ ⟫↑ {c = c1 p} l)) (φ2-of p (⟪ fr-μ ⟫↑ l)))
              isthistrue = {!!}

              isthistrue' : ⟪ fr-μ ⟫↓= (⟪ fr-μ ⟫↑ {c = c0} p,l)
                         == ⟪ fr-μ ⟫↓= (⟪ fr-μ ⟫↑ {c = c1 p} l)
              isthistrue' =
                ⟪ fr-μ ⟫↓= (⟪ fr-μ ⟫↑ {c = c0} p,l)
                  =⟨ ! (⟪ fr-μ ⟫■ {!idp!}) ⟩
                {!!}
                  =⟨ {!!} ⟩
                ⟪ fr-μ ⟫↓= (⟪ fr-μ ⟫↑ {c = c1 p} l) ∎ where
                  p0=p1 : (⟪ fr-μ ⟫↑ {c = c0} p,l)
                          == (⟪ fr-μ ⟫↑ {c = c1 p} l) [ {!!} ↓ {!idp!} ]
                  p0=p1 = {!!}

              isthistrue'' : (ap (τ FrP) (⟪ fr-μ ⟫⇅ {c = c0} p,l)) == (ap (τ FrP) (⟪ fr-μ ⟫⇅ {c = c1 p} l))
              isthistrue'' = {!idp!}

          lemma : (p : ρ P c)
               → (λ p' → ⟪ poly-id FrP ∣ fr-μ ⟫⇕ φ1 (p , p'))
                  == ⟪ poly-id FrP ∣ fr-μ ⟫⇕ (φ2-of p)
          lemma p = λ= (goal p)

      ρ-eq : (p : Σ (leafOf (node (c , φ))) ((λ l → Σ (leafOf (fst l)) (leafOf ∘ snd l)) ∘ ψ))
          → ⟪ ⊚-assoc-r FrP FrP FrP ▶ (poly-id FrP ∥ fr-μ) ▶ fr-μ ⟫↓ p
             == ⟪ (fr-μ ∥ poly-id FrP) ▶ fr-μ ⟫↓ p
             [ leafOf ↓ γ-eq ]
      ρ-eq p = ADMIT

    --FrM : PolyMonad I
    --MP FrM = FrP
    --η FrM = fr-η
    --μ FrM = fr-μ

    --η-left-law FrM = fr-η-left-law
    --η-right-law FrM = fr-η-right-law
    --μ-assoc-law FrM = ADMIT
