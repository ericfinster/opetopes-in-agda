{-# OPTIONS --without-K #-}

open import HoTT

open import FreeMonad
open import CartesianMorphism
open import WTypes
open import Polynomial
open import PolyMisc

module Simple where

  open ADMIT

  trans-eqv : {A : Type₀} (B : A → Type₀) (C : {a : A} → B a → Type₀)
              {a₀ a₁ : A} (e : a₀ == a₁) (b : B a₀) → C b ≃ C (transport B e b)
  trans-eqv B C idp b = ide _

  trans-lemma : {A : Type₀} (B : A → Type₀) (C : {a : A} → B a → Type₀)
                {a₀ a₁ : A} (e : a₀ == a₁) (b : B a₀) → C b → C (transport B e b)
  trans-lemma B C e b = –> (trans-eqv B C e b)

  record Monad : Type₁ where
    field
      -- I = J = Idx
      Idx : Type₀

      P : Poly Idx Idx

      -- unit and multiplication
      η : (i : Idx) → γ P i
      μ : {i : Idx} → (c : γ P i) → (δ : (p : ρ P c) → γ P (τ P p)) → γ P i

      -- equivalences of places (η, μ are Cartesian)
      ηp-eqv : {i : Idx} → ⊤ ≃ ρ P (η i) -- why not ⊥?
      μp-eqv : {i : Idx} {c : γ P i} (δ : (p : ρ P c) → γ P (τ P p))
            → Σ (ρ P c) ((ρ P) ∘ δ) ≃ ρ P (μ c δ)

    ηp : (i : Idx) → ρ P (η i)
    ηp i = –> ηp-eqv unit

    ηp-unique : (i : Idx) (p : ρ P (η i)) → p == ηp i
    ηp-unique i p = contr-has-all-paths (equiv-preserves-level ηp-eqv Unit-is-contr) p (ηp i)

    μp : {i : Idx} {c : γ P i} (δ : (p : ρ P c) → γ P (τ P p)) →
         (p : ρ P c) → (q : ρ P (δ p)) → ρ P (μ c δ)
    μp δ p q = –> (μp-eqv δ) (p , q)

    ρ-fst : {i : Idx} {c : γ P i} (δ : (p : ρ P c) → γ P (τ P p)) → ρ P (μ c δ) → ρ P c
    ρ-fst δ pp = fst (<– (μp-eqv δ) pp)

    ρ-snd : {i : Idx} {c : γ P i} (δ : (p : ρ P c) → γ P (τ P p)) → (pp : ρ P (μ c δ)) → ρ P (δ (ρ-fst δ pp))
    ρ-snd δ pp = snd (<– (μp-eqv δ) pp)

    field

      -- left square in Cartesian morphism
      ηp-compat : {i : Idx} → τ P (ηp i) == i
      μp-compat : {i : Idx} → {c : γ P i} → {δ : (p : ρ P c) → γ P (τ P p)}
               → (p : ρ P c) → (q : ρ P (δ p)) → τ P (μp δ p q) == τ P q

      -- monad laws
      unit-l : {i : Idx} → (c : γ P i) → μ c (λ p → η (τ P p)) == c
      unit-r : {i : Idx} → (δ : (p : ρ P (η i)) → γ P (τ P p))
            → δ (ηp i) == μ (η i) δ [ γ P ↓ ηp-compat ]

      assoc : {i : Idx} (c : γ P i) (δ : (p : ρ P c) → γ P (τ P p))
              (ε : (q : ρ P (μ c δ)) → γ P (τ P q))
           → μ c (λ p → μ (δ p) (λ q → transport (γ P) (μp-compat p q) (ε (μp δ p q)))) == μ (μ c δ) ε

  --
  -- The Free Monad
  --

  module  _ (Idx : Type₀) (P : Poly Idx Idx) where

    FrIdx : Type₀
    FrIdx = Idx

    data FrCn : (i : FrIdx) → Type₀ where
      leaf : ∀ i → FrCn i
      node : ∀ {i} → (c : γ P i) (δ : (p : ρ P c) → FrCn (τ P p)) → FrCn i

    frcn→w : ∀ {i} → FrCn i → W P i
    frcn→w (leaf _) = leaf _
    frcn→w (node c δ) = node (c , (λ p → frcn→w (δ p)))

    FrPl : ∀ {i} → FrCn i → Type₀
    FrPl (leaf i) = ⊤
    FrPl (node c δ) = Σ (ρ P c) (λ p → FrPl (δ p))

    FrTy : ∀ {i} {w : FrCn i} (n : FrPl w) → FrIdx
    FrTy {i} {leaf _} _ = i
    FrTy {w = node c δ} (p , p′) = FrTy {w = δ p} p′

    η-fr : (i : FrIdx) → FrCn i
    η-fr i = leaf i

    μ-fr : ∀ {i} (c : FrCn i) → (φ : (p : FrPl c) → FrCn (FrTy p)) → FrCn i
    μ-fr (leaf i) δ = δ unit
    μ-fr (node c φ) ψ = node c (λ p → μ-fr (φ p) (λ p′ → ψ (p , p′)))

    ηp-eqv-fr : {i : FrIdx} → ⊤ ≃ ⊤
    ηp-eqv-fr = (λ _ → _) , is-eq (λ _ → _) (λ _ → _) (λ _ → idp) (λ _ → idp)

    μp-eqv-fr : ∀ {i} {c : FrCn i} (δ : (p : FrPl c) → FrCn (FrTy p))
             → Σ (FrPl c) (FrPl ∘ δ) ≃ FrPl (μ-fr c δ)
    μp-eqv-fr {c = leaf _} _ = Σ₁-Unit
    μp-eqv-fr {c = node c φ} ψ = equiv-Σ-snd (λ p → μp-eqv-fr (λ p′ → ψ (p , p′))) ∘e Σ-assoc

    ηp-compat-fr : {i : FrIdx} → i == i
    ηp-compat-fr = idp

    μp-compat-fr : ∀ {i} (c : FrCn i) (δ : (p : FrPl c) → FrCn (FrTy p))
                   (p : FrPl c) (q : FrPl (δ p))
                → FrTy (–> (μp-eqv-fr δ) (p , q)) == FrTy q
    μp-compat-fr (leaf i) δ p q = idp
    μp-compat-fr (node c φ) ψ (p , q) r = μp-compat-fr (φ p) (λ p′ → ψ (p , p′)) q r

    --[ So far, just γ-eqs. We need to add ρ-eqs and talk about τ-eqs
    unit-l-fr : ∀ {i} (c : FrCn i)
             → μ-fr c (λ p → η-fr (FrTy p)) == c
    unit-l-fr {i} c = {!!}
      where
        w : W P i
        w = frcn→w c

        the-law : ⊚-unit-l (FrP P) ▶ (fr-η P ∥ poly-id (FrP P)) ▶ fr-μ P ≈ poly-id (FrP P)
        the-law = fr-η-left-law P

        derivᵣ : γ-map (poly-id (FrP P)) {j = i} w == w
        derivᵣ = idp

        derivₗ : γ-map (⊚-unit-l (FrP P) ▶ (fr-η P ∥ poly-id (FrP P)) ▶ fr-μ P) {j = i} w ==
                 frcn→w (μ-fr c (λ p → η-fr (FrTy p)))
        derivₗ =
          γ-map (⊚-unit-l (FrP P) ▶ (fr-η P ∥ poly-id (FrP P)) ▶ fr-μ P) {j = i} w
            =⟨ idp ⟩
          γ-map (fr-μ P) (frcn→w c , (λ q → leaf (leafType q)))
            =⟨ {!γ-map (fr-μ P)!} ⟩
          {!!}
            =⟨ {!!} ⟩
          frcn→w (μ-fr c (λ p → leaf (FrTy p)))
            =⟨ idp ⟩
          frcn→w (μ-fr c (λ p → η-fr (FrTy p))) ∎

--    unit-l-fr (leaf i) = idp
--    unit-l-fr (node c δ) = ap (λ x → node c x) (λ= (λ x → unit-l-fr (δ x)))

    unit-r-fr : ∀ {i} (δ : (p : ⊤) → FrCn i)
             → δ (–> (ηp-eqv-fr {i}) unit) == δ unit
    unit-r-fr {i} δ = idp

    assoc-fr : ∀ {i} (c : FrCn i) (δ : (p : FrPl c) → FrCn (FrTy p))
               (ε : (q : FrPl (μ-fr c δ)) → FrCn (FrTy q))
            → μ-fr c (λ p →
                       μ-fr (δ p) (λ q →
                                   transport FrCn (μp-compat-fr c δ p q) (ε (–> (μp-eqv-fr δ) (p , q)))))
               == μ-fr (μ-fr c δ) ε
    assoc-fr (leaf i) δ ε = idp
    assoc-fr (node c δ) φ ψ = ap (λ x → node c x) (λ= (λ x → assoc-fr (δ x) (λ p → φ (x , p)) (λ q → ψ (x , q))))
    --]

    Fr : Monad
    Monad.Idx Fr = FrIdx
    Monad.P Fr = FrP P
    Monad.η Fr = frcn→w ∘ η-fr
    Monad.μ Fr = {!!}
    Monad.ηp-eqv Fr {i} = {!!}
    Monad.μp-eqv Fr = {!!}
    Monad.ηp-compat Fr = {!!}
    Monad.μp-compat Fr {c = c} {δ = δ} = {!!}
    Monad.unit-l Fr = {!!}
    Monad.unit-r Fr = {!!}
    Monad.assoc Fr = {!!}
