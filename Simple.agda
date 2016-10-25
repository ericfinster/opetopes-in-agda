{-# OPTIONS --without-K #-}
--{-# OPTIONS --show-implicit #-}

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
                 δ (–> thm-ηp-eqv unit) == ⟪ μ ⟫ (⟪ η ⟫ lt , δ) [ γ P ↓ thm-ηp-compat ]
    thm-unit-r {i} δ = thm
      where
        c : γ P (τ P (–> thm-ηp-eqv unit))
        c = δ (–> thm-ηp-eqv unit)

        const-dec : ⟦ P ⟧⟦ ⟪ η ⟫ lt ≺ γ P ⟧
        const-dec = ⟪ poly-id P ∣ η ⟫⇕ (cst c)

        hyp : c == ⟪ μ ⟫ (⟪ η ⟫ lt , const-dec)
        hyp = ! ((γ≈ ∘ η-right-law) c)

        ρ-con : ∀ {i j} (p : i == j) (c : γ P i) (d : γ P j)
             → (e : c == d [ γ P ↓ p ]) → ρ P c ≃ ρ P d
        ρ-con idp c .c idp = ide (ρ P c)

        eq-pl : ∀ {i} → ρ P {i} (thm-η i) ≃ ρ P {τ P (–> (thm-ηp-eqv {i}) unit)} (⟪ η ⟫ lt)
        eq-pl = ⟦ P ↓ apd thm-η (⟪ η ⟫↓= lt) ⟧≃

        eq-ty : ∀ {i} (p : ρ P {i} (thm-η i))
            → τ P p == τ P (–> eq-pl p)
        eq-ty = ⟦ P ↓ apd thm-η (⟪ η ⟫↓= lt) ⟧↓=

        δ=const : (p : ρ P (thm-η i)) → δ p == const-dec (–> eq-pl p) [ γ P ↓ eq-ty p ]
        δ=const p = from-transp (γ P) (eq-ty p) lemma where
          lemma : transport (γ P) (eq-ty p) (δ p) == const-dec (–> eq-pl p)
          lemma =
            transport (γ P) (eq-ty p) (δ p) =⟨ idp ⟩
            coe (ap (γ P) (⟦ P ↓ apd (λ _ → ⟪ η ⟫ lt) (⟪ η ⟫↓= lt) ⟧↓= p)) (δ p) =⟨ {!!} ⟩
            {!const-dec (–> eq-pl p) !} =⟨ {!!} ⟩
            const-dec (–> eq-pl p) ∎
        --δ=const p = ↓-≺-out P
        --                    {X = γ P}
        --                    {i = i}
        --                    {i′ = {!–> eq-pl p!}}
        --                    {i=i′ = {!!}}
        --                    {c = {!!}}
        --                    {c′ = {!!}}
        --                    {φ = {!!}}
        --                    {φ′ = {!!}}
        --                    {!!} -- φ=φ′
        --                    {p = {!!}}
        --                    {p′ = {!!}}
        --                    {!!} where

        --  lem1 : i == τ P (–> thm-ηp-eqv unit)
        --  lem1 = ! {!thm-ηp-compat {i}!} --?

        --  lem2 : thm-η i == ⟪ η ⟫ lt [ γ P ↓ lem1 ]
        --  lem2 = {!idp!}

        --  lem3 : δ == const-dec [ ⟦ P ⟧≺ (γ P) ↓ pair= lem1 lem2 ]
        --  lem3 = {!!}

        --  lem4 : p == –> eq-pl p [ ρ-Σ P ↓ pair= lem1 lem3 ]
        --  lem4 = {!!}

        thm : δ (–> thm-ηp-eqv unit) == ⟪ μ ⟫ (⟪ η ⟫ lt , δ) [ γ P ↓ thm-ηp-compat ]
        thm = {!!}


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
