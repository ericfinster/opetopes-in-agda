{-# OPTIONS --without-K #-}
-- {-# OPTIONS --show-implicit #-}

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
      ηp-eqv : {i : Idx} → ⊤ ≃ ρ P (η i)
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

    thm-idx : Type₀
    thm-idx = I

    thm-P : Poly I I
    thm-P = P

    thm-η : (i : I) → γ P i
    thm-η i = ⟪ η ⟫ lt

    thm-μ : {i : I} (c : γ P i) (δ : (p : ρ P c) → γ P (τ P p)) → γ P i
    thm-μ c δ = ⟪ μ ⟫ (c , δ)

    thm-ηp-eqv : {i : I} → ⊤ ≃ ρ P (thm-η i)
    thm-ηp-eqv = (λ _ → η-plc M _) ,
      (is-eq (λ _ → η-plc M _) (λ _ → unit) (snd (η-plc-contr M _)) (λ _ → idp))

    thm-μp-eqv : {i : thm-idx} {c : γ P i} (δ : (p : ρ P c) → γ P (τ P p)) →
                 Σ (ρ P c) ((ρ P) ∘ δ) ≃ ρ P (thm-μ c δ)
    thm-μp-eqv {c = c} δ = ⟪ μ ⟫≃ {c = (c , δ)}

    thm-ηp-compat : {i : thm-idx} → τ P (–> thm-ηp-eqv unit) == i
    thm-ηp-compat = ! (⟪ η ⟫↓= lt)

    thm-μp-compat : {i : thm-idx} {c : γ P i} {δ : (p : ρ P c) → γ P (τ P p)}
                    (p : ρ P c) (q : ρ P (δ p)) → τ P (–> (thm-μp-eqv δ) (p , q)) == τ P q
    thm-μp-compat p q = ! (⟪ μ ⟫↓= (p , q))

    thm-unit-l : {i : thm-idx} (c : γ P i) → thm-μ c (λ p → thm-η (τ P p)) == c
    thm-unit-l = γ≈ ∘ η-left-law

    thm-unit-r : {i : thm-idx} (δ : ⟦ P ⟧⟦ ⟪ η ⟫ lt ≺ γ P ⟧) →
                 δ (⟪ η ⟫↓ lt) == ⟪ μ ⟫ (⟪ η ⟫ lt , δ) [ γ P ↓ thm-ηp-compat ]
    thm-unit-r {i} δ = thm
      where

        i' : I
        i' = (τ P (⟪ η ⟫↓ lt))

        i=i' : i == i'
        i=i' = ⟪ η ⟫↓= lt
        
        c : γ P i'
        c = δ (⟪ η ⟫↓ lt)
        
        const-dec : ⟦ P ⟧⟦ ⟪ η ⟫ {j = i'} lt ≺ γ P ⟧
        const-dec = ⟪ poly-id P ∣ η ⟫⇕ (cst c)

        unit-law : ⟪ μ ⟫ (⟪ η ⟫ lt , const-dec) == c
        unit-law = (γ≈ ∘ η-right-law) c

        const-dec-coh : δ (⟪ η ⟫↓ {j = i} lt) == (const-dec (⟪ η ⟫↓ {j = i'} lt)) [ γ P ↓ ⟪ η ⟫↓= lt ]
        const-dec-coh = ⟪ poly-id P ∣ η ⟫⇕-coh (cst c) lt

        a-goal : δ == const-dec [ ⟦ P ⟧≺ (γ P) ↓ pair= i=i' (apd (λ x → ⟪ η ⟫ {j = x} lt) i=i') ]
        a-goal = η-dec-unique M i=i' δ const-dec {!!}
          
                   -- (q : δ₀ (⟪ η ⟫↓ lt) == δ₁ (⟪ η ⟫↓ lt) [ γ P ↓ ap (λ j → τ P (⟪ η ⟫↓ {j = j} lt)) p ])

        next-goal : ⟪ μ ⟫ (⟪ η ⟫ lt , δ) == ⟪ μ ⟫ (⟪ η ⟫ lt , const-dec) [ γ P ↓ ⟪ η ⟫↓= lt ]
        next-goal = μ-inv M {i₀ = i} {i₁ = i'} (⟪ η ⟫ lt) (⟪ η ⟫ lt) δ const-dec i=i'
                          (apd (λ x → ⟪ η ⟫ {j = x} lt) i=i')
                          a-goal

        thm : δ (⟪ η ⟫↓ lt) == ⟪ μ ⟫ (⟪ η ⟫ lt , δ) [ γ P ↓ thm-ηp-compat ]
        thm = !ᵈ (next-goal ∙'ᵈ unit-law)

    theorem : Monad
    Monad.Idx theorem = thm-idx
    Monad.P theorem = P
    Monad.η theorem = thm-η
    Monad.μ theorem = thm-μ
    Monad.ηp-eqv theorem = thm-ηp-eqv
    Monad.μp-eqv theorem = thm-μp-eqv
    Monad.ηp-compat theorem = thm-ηp-compat
    Monad.μp-compat theorem = thm-μp-compat
    Monad.unit-l theorem = thm-unit-l
    Monad.unit-r theorem = thm-unit-r
    Monad.assoc theorem = {!!}
