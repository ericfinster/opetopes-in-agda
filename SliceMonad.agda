{-# OPTIONS --without-K #-}

open import HoTT

open import Polynomial
open import CartesianMorphism
open import PolynomialMonad
open import PolyMisc

module SliceMonad where

  module _ {ℓ} {I : Type ℓ} (M : PolyMonad I) where

    open PolyMonad
    open ADMIT

    data SlCn : {i : I} → γ (P M) i → Type ℓ where
      dot : (i : I) → SlCn {i = i} (⟪ η M ⟫ lt)
      box : {i : I} → (c : γ (P M) i) →
            (δ : (p : ρ (P M) c) → γ (P M) (τ (P M) p)) →
            (ε : (p : ρ (P M) c) → SlCn (δ p)) →
            SlCn (⟪ μ M ⟫ (c , δ))

    SlPl : {i : I} → {c : γ (P M) i} → (w : SlCn c) → Type ℓ
    SlPl (dot i) = Lift ⊥
    SlPl (box c δ ε) = Lift {j = ℓ} ⊤ ⊔ Σ (ρ (P M) c) (λ p → SlPl (ε p))

    B : Type ℓ
    B = Σ I (γ (P M))

    SlCn' : B → Type ℓ
    SlCn' (i , c) = SlCn c

    {-# TERMINATING #-}
    SlP : Poly B B
    γ SlP (i , c) = SlCn c
    ρ SlP {i , c} n = SlPl n
    τ SlP {i , _} {dot .i} (lift ())
    τ SlP {i , _} {box c δ ε} (inl (lift unit)) = i , c
    τ SlP {i , _} {box c δ ε} (inr (p , n)) = τ SlP n

    sl-η : IdP B ⇝ SlP
    γ-map sl-η {i , c} _ = transport SlCn (γ≈ (η-left-law M c)) (box c (λ p → ⟪ η M ⟫ lt) (λ p → dot (τ (P M) p)))
    ρ-eqv sl-η {i , c} {lift unit} = {!!} ∘e lemma

       where lemma : Lift {j = ℓ} ⊤ ≃ SlPl (box c (λ p → ⟪ η M ⟫ lt) (λ p → dot (τ (P M) p)))
             lemma = (λ { (lift unit) → inl lt }) , is-eq _ (λ { p → lt })
                     (λ { (inl (lift unit)) → idp ; (inr (_ , lift ())) })
                     (λ { (lift unit) → idp })

    τ-coh sl-η p = {!!}

    sl-graft : {i : I} → {c : γ (P M) i} → (w : SlCn c) →
               (δ : (p : ρ (P M) c) → γ (P M) (τ (P M) p)) →
               (ε : (p : ρ (P M) c) → SlCn (δ p)) → SlCn (⟪ μ M ⟫ (c , δ))
    sl-graft (dot i) δ₁ ε₁ = {!!} -- transport! SlCn' (pair= (τ-coh (η M) lt) {!γ≈ (η-left-law M (γ-map (η M) lt))!}) (ε₁ (⟪ η M ⟫↓ lt))

      where ηi : γ (P M) i
            ηi = ⟪ η M ⟫ lt

            ηp : ρ (P M) ηi
            ηp = ⟪ η M ⟫↓ lt

            ε' : SlCn (δ₁ ηp)
            ε' = ε₁ ηp

            test : {!!} == ηi
            test = γ≈ (η-left-law M ηi)

    sl-graft (box c δ ε) δ₁ ε₁ = transport! SlCn {!!} (box c (λ p → ⟪ μ M ⟫ (δ p , α p)) IH)

      where α : (p : ρ (P M) c) → (q : ρ (P M) (δ p)) → γ (P M) (τ (P M) q)
            α p q = {!!}

            β : (p : ρ (P M) c) → (q : ρ (P M) (δ p)) → SlCn (α p q)
            β p q = {!!}

            IH : (p : ρ (P M) c) → SlCn (⟪ μ M ⟫ (δ p , α p))
            IH p = sl-graft (ε p) (α p) (β p)

    sl-graft-ρ-here : {i : I} → {c : γ (P M) i} → (w : SlCn c) →
                      (δ : (p : ρ (P M) c) → γ (P M) (τ (P M) p)) →
                      (ε : (p : ρ (P M) c) → SlCn (δ p)) → (n : SlPl w) → SlPl (sl-graft w δ ε)
    sl-graft-ρ-here (dot i) δ ε (lift ())
    sl-graft-ρ-here (box c δ ε) δ₁ ε₁ (inl (lift unit)) = {!!} -- ⟦ SlP ↓ from-transp! SlCn idp {!!} ⟧↓ {!!}
    sl-graft-ρ-here (box c δ ε) δ₁ ε₁ (inr (p , n)) = {!!}

    sl-μ-γ : {i : I} {c : γ (P M) i} (w : SlCn c) (κ : (p : ρ SlP w) → SlCn' (τ SlP p)) → SlCn c
    sl-μ-γ (dot i) κ = dot i
    sl-μ-γ (box c δ ε) κ = sl-graft (κ (inl lt)) δ (λ p → sl-μ-γ (ε p) (λ n → κ (inr (p , n))))

    sl-μ-ρ : {i : I} {c : γ (P M) i} (w : SlCn c) (κ : (p : ρ SlP w) → SlCn (snd (τ SlP p))) →
             Σ (SlPl w) (SlPl ∘ κ) → SlPl (sl-μ-γ w κ)
    sl-μ-ρ (dot i) k (lift () , n₁)
    sl-μ-ρ (box c δ ε) k (n₀ , n₁) = {!!}

    {-# TERMINATING #-}
    sl-μ : SlP ⊚ SlP ⇝ SlP
    γ-map sl-μ (w , κ) = sl-μ-γ w κ
    ρ-eqv sl-μ {c = w , k} = sl-μ-ρ w k , {!!}
    τ-coh sl-μ p = {!!}
