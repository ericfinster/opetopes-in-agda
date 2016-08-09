{-# OPTIONS --without-K #-}

open import HoTT

module Simple where

  trans-lemma : {A : Type₀} (B : A → Type₀) (C : {a : A} → B a → Type₀)
                {a₀ a₁ : A} (e : a₀ == a₁) (b : B a₀) → C b → C (transport B e b)
  trans-lemma B C idp b c = c

  record Monad : Type₁ where
    field

      Idx : Type₀

      γ : Idx → Type₀
      ρ : {i : Idx} → (c : γ i) → Type₀
      τ : {i : Idx} → {c : γ i} → (p : ρ c) → Idx
      
      η : (i : Idx) → γ i
      μ : {i : Idx} → (c : γ i) → (δ : (p : ρ c) → γ (τ p)) → γ i

      ηp-eqv : {i : Idx} → ⊤ ≃ ρ (η i)
      μp-eqv : {i : Idx} {c : γ i} (δ : (p : ρ c) → γ (τ p)) →
               Σ (ρ c) (ρ ∘ δ) ≃ ρ (μ c δ)

    ηp : (i : Idx) → ρ (η i)
    ηp i = –> ηp-eqv unit

    μp : {i : Idx} {c : γ i} (δ : (p : ρ c) → γ (τ p)) →
         (p : ρ c) → (q : ρ (δ p)) → ρ (μ c δ)
    μp δ p q = –> (μp-eqv δ) (p , q)

    field
    
      ηp-compat : {i : Idx} → τ (ηp i) == i
      μp-compat : {i : Idx} → {c : γ i} → {δ : (p : ρ c) → γ (τ p)} →
                  (p : ρ c) → (q : ρ (δ p)) → τ (μp δ p q) == τ q

      unit-l : {i : Idx} → (c : γ i) → μ c (λ p → η (τ p)) == c
      unit-r : {i : Idx} → (δ : (p : ρ (η i)) → γ (τ p)) →
                δ (ηp i) == μ (η i) δ [ γ ↓ ηp-compat {i} ]

      assoc : {i : Idx} → (c : γ i) →
              (δ : (p : ρ c) → γ (τ p)) →
              (ε : (q : ρ (μ c δ)) → γ (τ q)) →
              μ c (λ p → μ (δ p) (λ q → transport γ (μp-compat {δ = δ} p q) (ε (μp δ p q)))) == μ (μ c δ) ε
             
  --
  --  The Slice Monad
  --

  module Slice (M : Monad) where

    open Monad M
    
    SlIdx : Type₀
    SlIdx = Σ Idx γ

    data SlCn : {i : Idx} → (c : γ i) → Type₀ where
      dot : (i : Idx) → SlCn (η i)
      box : {i : Idx} → (c : γ i) →
            (δ : (p : ρ c) → γ (τ p)) →
            (ε : (p : ρ c) → SlCn (δ p)) →
            SlCn (μ c δ)

    SlCn' : SlIdx → Type₀
    SlCn' (i , c) = SlCn c
  
    SlPl : {i : Idx} {c : γ i} (w : SlCn c) → Type₀
    SlPl (dot i) = ⊥
    SlPl (box c δ ε) = ⊤ ⊔ Σ (ρ c) (λ p → SlPl (ε p))

    SlTy : {i : Idx} {c : γ i} (w : SlCn c) (n : SlPl w) → SlIdx
    SlTy (dot i) ()
    SlTy (box c δ ε) (inl unit) = _ , c
    SlTy (box c δ ε) (inr (p , n)) = SlTy (ε p) n
  
  -- SlGrft : (M : Monad) {i : Idx M} {c : γ M i} (w : SlCn M c)
  --          (δ : (p : ρ M c) → γ M (τ M p))
  --          (ε : (p : ρ M c) → SlCn M (δ p)) →
  --          SlCn M (μ M c δ)
  -- SlGrft M (dot i) δ ε = transport (SlCn' M) (pair= (ηp-compat M) (unit-r M δ)) (ε (ηp M i))
  -- SlGrft M (box c δ ε) δ₁ ε₁ = transport (SlCn M) (assoc M c δ δ₁) (box c δ' IH)

  --   where δ' : (p : ρ M c) → γ M (τ M p)
  --         δ' p = μ M (δ p) (λ q → transport (γ M) (μp-compat M {δ = δ} p q) (δ₁ (μp M p q)))

  --         IH : (p : ρ M c) → SlCn M (δ' p)
  --         IH p = SlGrft M (ε p) _ (λ q → transport (SlCn' M) (pair= (μp-compat M {δ = δ} p q) (from-transp (γ M) _ idp)) (ε₁ (μp M p q)))

  -- SlGrftPl₀ : (M : Monad) {i : Idx M} {c : γ M i} (w : SlCn M c)
  --             (δ : (p : ρ M c) → γ M (τ M p))
  --             (ε : (p : ρ M c) → SlCn M (δ p)) →
  --             (n : SlPl M w) → SlPl M (SlGrft M w δ ε)
  -- SlGrftPl₀ M (dot i) δ ε ()
  -- SlGrftPl₀ M (box c δ ε) δ₁ ε₁ (inl unit) = trans-lemma (SlCn M) (SlPl M) (assoc M c δ δ₁) _ (inl unit)
  -- SlGrftPl₀ M (box c δ ε) δ₁ ε₁ (inr (p , n)) = trans-lemma (SlCn M) (SlPl M) (assoc M c δ δ₁) _ (inr (p , IH p n)) 

  --   where δ' : (p : ρ M c) → γ M (τ M p)
  --         δ' p = μ M (δ p) (λ q → transport (γ M) (μp-compat M {δ = δ} p q) (δ₁ (μp M p q)))

  --         grft-IH : (p : ρ M c) → SlCn M (δ' p)
  --         grft-IH p = SlGrft M (ε p) _ (λ q → transport (SlCn' M) (pair= (μp-compat M {δ = δ} p q) (from-transp (γ M) _ idp)) (ε₁ (μp M p q)))

  --         IH : (p : ρ M c) → (n : SlPl M (ε p)) → SlPl M (grft-IH p)
  --         IH p n = SlGrftPl₀ M (ε p) _ _ n

  -- SlGrftPl₁ : (M : Monad) {i : Idx M} {c : γ M i} (w : SlCn M c)
  --             (δ : (p : ρ M c) → γ M (τ M p))
  --             (ε : (p : ρ M c) → SlCn M (δ p)) →
  --             (p : ρ M c) → (n : SlPl M (ε p)) → SlPl M (SlGrft M w δ ε)
  -- SlGrftPl₁ M (dot i) δ ε p n = {!!}
  -- SlGrftPl₁ M (box c δ ε) δ₁ ε₁ p n = trans-lemma (SlCn M) (SlPl M) (assoc M c δ δ₁) _ (inr {!!})

  -- -- Right.  What you see now is that you actually have to split the place of
  -- -- the multiplication here in order to call out to the induction hypothesis.
  -- -- So this means you'll actually have to spell out the place equivalences and
  -- -- rewrite this so that you use them.
