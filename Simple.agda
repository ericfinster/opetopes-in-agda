{-# OPTIONS --without-K #-}

open import HoTT

open import CartesianMorphism
open import Polynomial
open import PolyMisc
open import PolynomialMonad

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
  -- A Polynomial monad is a simple monad
  --

  module _ {I : Type₀} (M : PolyMonad I) where

    open PolyMonad M

    theorem : Monad
    Monad.Idx theorem = I
    Monad.P theorem = P
    Monad.η theorem _ = ⟪ η ⟫ _
    Monad.μ theorem c δ = ⟪ μ ⟫ (c , δ)
    Monad.ηp-eqv theorem = (λ _ → η-plc M _) ,
      (is-eq (λ _ → η-plc M _) (λ _ → unit) (snd (η-plc-contr M _)) (λ _ → idp))
    Monad.μp-eqv theorem _ = ⟪ μ ⟫↓ , is-eq ⟪ μ ⟫↓ ⟪ μ ⟫↑  ⟪ μ ⟫⇅ ⟪ μ ⟫⇵
    Monad.ηp-compat theorem =  ! (⟪ η ⟫↓= lt)
    Monad.μp-compat theorem p q = ! (⟪ μ ⟫↓= (p , q))
    Monad.unit-l theorem = γ≈ ∘ η-left-law
    --Monad.unit-r theorem {i} δ = from-transp (γ P) (! (⟪ η ⟫↓= lt)) lemma
    Monad.unit-r theorem {i} δ = from-transp (γ P) (! (⟪ η ⟫↓= lt)) lemma
      where
        lemma : transport (γ P) (! (⟪ η ⟫↓= lt)) (δ (⟪ η ⟫↓ lt)) == ⟪ μ ⟫ (⟪ η ⟫ lt , δ)
        lemma = transport (γ P) (! (⟪ η ⟫↓= lt)) (δ (⟪ η ⟫↓ lt))
                  =⟨ {!transport (γ P) (! (⟪ η ⟫↓= lt)) (δ (⟪ η ⟫↓ lt))!} ⟩
                {!f!}
                  =⟨ {!transport (γ P) (! (⟪ η ⟫↓= lt)) (δ (⟪ η ⟫↓ lt))!} ⟩
                ⟪ μ ⟫ (⟪ η ⟫ lt , δ) ∎
    --Monad.unit-r theorem {i} δ = ⟪ η ∣ {!!} ⟫⇓ {!!} {!!}
    Monad.assoc theorem c δ ε = {!!}
