{-# OPTIONS --without-K #-}

open import HoTT

module Simple where

  open ADMIT

  trans-eqv : {A : Type₀} (B : A → Type₀) (C : {a : A} → B a → Type₀)
              {a₀ a₁ : A} (e : a₀ == a₁) (b : B a₀) → C b ≃ C (transport B e b)
  trans-eqv B C idp b = ide _

  trans-lemma : {A : Type₀} (B : A → Type₀) (C : {a : A} → B a → Type₀)
                {a₀ a₁ : A} (e : a₀ == a₁) (b : B a₀) → C b → C (transport B e b)
  trans-lemma B C e b = –> (trans-eqv B C e b)

  record Poly : Type₁ where
    constructor _≺_[_]
    field
      Idx : Type₀

      γ : Idx → Type₀
      ρ : {i : Idx} → (c : γ i) → Type₀
      τ : {i : Idx} → {c : γ i} → (p : ρ c) → Idx

  record Monad : Type₁ where
    field
      -- I = J = Idx
      Idx : Type₀

      -- polynomial functor
      γ : Idx → Type₀
      ρ : {i : Idx} → (c : γ i) → Type₀
      τ : {i : Idx} → {c : γ i} → (p : ρ c) → Idx

      -- unit and multiplication
      η : (i : Idx) → γ i
      μ : {i : Idx} → (c : γ i) → (δ : (p : ρ c) → γ (τ p)) → γ i

      -- equivalences of places (η, μ are Cartesian)
      ηp-eqv : {i : Idx} → ⊤ ≃ ρ (η i) -- why not ⊥?
      μp-eqv : {i : Idx} {c : γ i} (δ : (p : ρ c) → γ (τ p))
            → Σ (ρ c) (ρ ∘ δ) ≃ ρ (μ c δ)

    ηp : (i : Idx) → ρ (η i)
    ηp i = –> ηp-eqv unit

    ηp-unique : (i : Idx) (p : ρ (η i)) → p == ηp i
    ηp-unique i p = contr-has-all-paths (equiv-preserves-level ηp-eqv Unit-is-contr) p (ηp i)

    μp : {i : Idx} {c : γ i} (δ : (p : ρ c) → γ (τ p)) →
         (p : ρ c) → (q : ρ (δ p)) → ρ (μ c δ)
    μp δ p q = –> (μp-eqv δ) (p , q)

    ρ-fst : {i : Idx} {c : γ i} (δ : (p : ρ c) → γ (τ p)) → ρ (μ c δ) → ρ c
    ρ-fst δ pp = fst (<– (μp-eqv δ) pp)

    ρ-snd : {i : Idx} {c : γ i} (δ : (p : ρ c) → γ (τ p)) → (pp : ρ (μ c δ)) → ρ (δ (ρ-fst δ pp))
    ρ-snd δ pp = snd (<– (μp-eqv δ) pp)

    field

      -- left square in Cartesian morphism
      ηp-compat : {i : Idx} → τ (ηp i) == i
      μp-compat : {i : Idx} → {c : γ i} → {δ : (p : ρ c) → γ (τ p)}
               → (p : ρ c) → (q : ρ (δ p)) → τ (μp δ p q) == τ q

      -- monad laws
      unit-l : {i : Idx} → (c : γ i) → μ c (λ p → η (τ p)) == c
      unit-r : {i : Idx} → (δ : (p : ρ (η i)) → γ (τ p))
            → δ (ηp i) == μ (η i) δ [ γ ↓ ηp-compat ]

      assoc : {i : Idx} (c : γ i) (δ : (p : ρ c) → γ (τ p))
              (ε : (q : ρ (μ c δ)) → γ (τ q))
           → μ c (λ p → μ (δ p) (λ q → transport γ (μp-compat p q) (ε (μp δ p q)))) == μ (μ c δ) ε

      unit-l-ρ : {i : Idx} (c : γ i) (p : ρ c) (p′ : ρ (η (τ p)))
              → μp (λ r → η (τ r)) p p′ == ADMIT

  --
  -- The Free Monad
  --

  module  _ (P : Poly) where
    open Poly P
    open Monad hiding (Idx; γ; ρ; τ)

    FrIdx : Type₀
    FrIdx = Idx

    data FrCn : (i : FrIdx) → Type₀ where
      leaf : ∀ i → FrCn i
      node : ∀ {i} → (c : γ i) (δ : (p : ρ c) → FrCn (τ p)) → FrCn i

    FrPl : ∀ {i} → FrCn i → Type₀
    FrPl (leaf i) = ⊤
    FrPl (node c δ) = Σ (ρ c) (λ p → FrPl (δ p))

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

    -- μ-pl-fr : ∀ {i} (c : FrCn i) (δ : (p : FrPl c) → FrCn (FrTy p)) → Σ (FrPl c) (FrPl ∘ δ) → FrPl (μ-fr c δ)
    -- μ-pl-fr (leaf i) δ (unit , p) = p
    -- μ-pl-fr (node c δ) φ ((p , p′) , p,p′) = p , {!!}

    -- μ-pl-fr! : ∀ {i} {c : FrCn i} (δ : (p : FrPl c) → FrCn (FrTy p)) → FrPl (μ-fr c δ) → Σ (FrPl c) (FrPl ∘ δ)
    -- μ-pl-fr! = {!!}

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
    unit-l-fr (leaf i) = idp
    unit-l-fr (node c δ) = ap (λ x → node c x) (λ= (λ x → unit-l-fr (δ x)))

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

    Fr : Poly → Monad
    Monad.Idx (Fr P) = FrIdx
    Monad.γ (Fr M) = FrCn
    Monad.ρ (Fr M) = FrPl
    Monad.τ (Fr M) = FrTy
    η (Fr M) = η-fr
    μ (Fr M) = μ-fr
    ηp-eqv (Fr M) {i} = ηp-eqv-fr {i}
    μp-eqv (Fr M) = μp-eqv-fr
    ηp-compat (Fr M) = ηp-compat-fr
    μp-compat (Fr M) {c = c} {δ = δ} = μp-compat-fr c δ
    unit-l (Fr M) = unit-l-fr
    unit-r (Fr M) = unit-r-fr
    assoc (Fr M) = assoc-fr
    -----
    unit-l-ρ (Fr M) = ADMIT

  --
  --  The Slice Monad
  --

  module _ (M : Monad) where

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

    module Local {i : Idx} (c : γ i)
                 (δ : (p : ρ c) → γ (τ p))
                 (ε : (p : ρ c) → SlCn (δ p))
                 (δ₁ : (p : ρ (μ c δ)) → γ (τ p))
                 (ε₁ : (p : ρ (μ c δ)) → SlCn (δ₁ p)) where

      δ₁' : (p : ρ c) → (q : ρ (δ p)) → γ (τ q)
      δ₁' p q = transport γ (μp-compat p q) (δ₁ (μp δ p q))

      ε₁' : (p : ρ c) → (q : ρ (δ p)) → SlCn (δ₁' p q)
      ε₁' p q = transport SlCn' (pair= (μp-compat p q) (from-transp γ _ idp)) (ε₁ (μp δ p q))

      δ' : (p : ρ c) → γ (τ p)
      δ' p = μ (δ p) (δ₁' p)

    SlGrft : {i : Idx} {c : γ i} (w : SlCn c)
             (δ : (p : ρ c) → γ (τ p))
             (ε : (p : ρ c) → SlCn (δ p)) →
             SlCn (μ c δ)
    SlGrft (dot i) δ ε = transport SlCn' (pair= ηp-compat (unit-r δ)) (ε (ηp i))
    SlGrft (box c δ ε) δ₁ ε₁ = transport SlCn (assoc c δ δ₁) (box c δ' (λ p → SlGrft (ε p) (δ₁' p) (ε₁' p)))
      where open Local c δ ε δ₁ ε₁

    SlGrftPl₀ : {i : Idx} {c : γ i} (w : SlCn c)
                (δ : (p : ρ c) → γ (τ p))
                (ε : (p : ρ c) → SlCn (δ p)) →
                (n : SlPl w) → SlPl (SlGrft w δ ε)
    SlGrftPl₀ (dot i) δ ε ()
    SlGrftPl₀ (box c δ ε) δ₁ ε₁ (inl unit) = trans-lemma SlCn SlPl (assoc c δ δ₁) _ (inl unit)
    SlGrftPl₀ (box c δ ε) δ₁ ε₁ (inr (p , n)) =
      trans-lemma SlCn SlPl (assoc c δ δ₁) _ (inr (p , SlGrftPl₀ (ε p) (δ₁' p) (ε₁' p) n))
        where open Local c δ ε δ₁ ε₁

    SlGrftPl₁ : {i : Idx} {c : γ i} (w : SlCn c)
                (δ : (p : ρ c) → γ (τ p))
                (ε : (p : ρ c) → SlCn (δ p)) →
                (p : ρ c) → (n : SlPl (ε p)) → SlPl (SlGrft w δ ε)
    SlGrftPl₁ (dot i) δ ε p n = –> (trans-eqv SlCn' SlPl (pair= ηp-compat (unit-r δ)) (ε (ηp i))) (transport (SlPl ∘ ε) (ηp-unique i p) n)
    SlGrftPl₁ (box c δ ε) δ₁ ε₁ p n = trans-lemma SlCn SlPl (assoc c δ δ₁) _ (inr (p₀ , IH))

      where open Local c δ ε δ₁ ε₁

            p₀ = ρ-fst δ p
            p₁ = ρ-snd δ p

            lemma : ε₁ p == ε₁' p₀ p₁ [ SlCn' ↓ pair= ADMIT ADMIT ]
            lemma = ADMIT

            IH : SlPl (SlGrft (ε p₀) (δ₁' p₀) (ε₁' p₀))
            IH = SlGrftPl₁ (ε p₀) (δ₁' p₀) (ε₁' p₀) p₁ ADMIT
            -- right, well, the last guy is just "n" but the
            -- type has to be fixed up...

    SlSplitPl : {i : Idx} {c : γ i} (w : SlCn c)
                (δ : (p : ρ c) → (γ (τ p)))
                (ε : (p : ρ c) → SlCn (δ p)) →
                (n : SlPl (SlGrft w δ ε)) → SlPl w ⊔ Σ (ρ c) (λ p → SlPl (ε p))
    SlSplitPl (dot i) δ₁ ε₁ n = inr (ηp i , <– (trans-eqv SlCn' SlPl (pair= ηp-compat (unit-r δ₁)) (ε₁ (ηp i))) n)
    SlSplitPl (box c δ ε) δ₁ ε₁ n with <– (trans-eqv SlCn SlPl (assoc c δ δ₁) _) n
    SlSplitPl (box c δ ε) δ₁ ε₁ n | inl unit = inl (inl unit)
    SlSplitPl (box c δ ε) δ₁ ε₁ n | inr (p , n') with let open Local c δ ε δ₁ ε₁ in SlSplitPl (ε p) (δ₁' p) (ε₁' p) n'
    SlSplitPl (box c δ ε) δ₁ ε₁ n | inr (p , n') | (inl n₀) = inl (inr (p , n₀))
    SlSplitPl (box c δ ε) δ₁ ε₁ n | inr (p , n') | (inr (q , n₀)) = inr (μp δ p q , <– (trans-eqv SlCn' SlPl (pair= (μp-compat p q) (from-transp γ (μp-compat p q) idp)) (ε₁ (μp δ p q))) n₀)
      where open Local c δ ε δ₁ ε₁

  open Monad

  η-sl : (M : Monad) (b : SlIdx M) → SlCn' M b
  η-sl M (i , c) = transport (SlCn M) (unit-l M c) (box c (λ p → η M (τ M p)) (λ p → dot (τ M p)))

  μ-sl : (M : Monad) {b : SlIdx M} (w : SlCn' M b) (κ : (p : SlPl M w) → SlCn' M (SlTy M w p)) → SlCn' M b
  μ-sl M (dot i) κ = dot i
  μ-sl M (box c δ ε) κ = SlGrft M (κ (inl unit)) δ (λ p → μ-sl M (ε p) (λ q → κ (inr (p , q))))

  μ-pl : (M : Monad) {b : SlIdx M} (w : SlCn' M b) (κ : (p : SlPl M w) → SlCn' M (SlTy M w p)) →
         Σ (SlPl M w) (SlPl M ∘ κ) → SlPl M (μ-sl M w κ)
  μ-pl M (dot i) κ (() , n₁)
  μ-pl M (box c δ ε) κ (inl unit , n₁) = SlGrftPl₀ M (κ (inl unit)) δ (λ p → μ-sl M (ε p) (λ q → κ (inr (p , q)))) n₁
  μ-pl M (box c δ ε) κ (inr (p , n₀) , n₁) = SlGrftPl₁ M (κ (inl unit)) δ (λ p → μ-sl M (ε p) (λ q → κ (inr (p , q)))) p IH

    where κ' : (n : SlPl M (ε p)) → SlCn' M (SlTy M (ε p) n)
          κ' n = κ (inr (p , n))

          IH : SlPl M (μ-sl M (ε p) κ')
          IH = μ-pl M (ε p) κ' (n₀ , n₁)

  μ-pl-inv : (M : Monad) {b : SlIdx M} (w : SlCn' M b) (κ : (p : SlPl M w) → SlCn' M (SlTy M w p)) →
             SlPl M (μ-sl M w κ) → Σ (SlPl M w) (SlPl M ∘ κ)
  μ-pl-inv M (dot i) κ ()
  μ-pl-inv M (box c δ ε) κ n with SlSplitPl M (κ (inl unit)) δ (λ p → μ-sl M (ε p) (λ q → κ (inr (p , q)))) n
  μ-pl-inv M (box c δ ε) κ n | inl n₁ = inl unit , n₁
  μ-pl-inv M (box c δ ε) κ n | inr (p , n₁) = inr (p , fst IH) , snd IH

    where IH : Σ (SlPl M (ε p)) (λ n' → SlPl M (κ (inr (p , n'))))
          IH = μ-pl-inv M (ε p) (λ n' → κ (inr (p , n'))) n₁

  Sl : Monad → Monad
  Idx (Sl M) = SlIdx M
  γ (Sl M) = SlCn' M
  ρ (Sl M) w = SlPl M w
  τ (Sl M) n = SlTy M _ n
  η (Sl M) = η-sl M
  μ (Sl M) = μ-sl M
  ηp-eqv (Sl M) = ADMIT
  μp-eqv (Sl M) κ = μ-pl M _ κ , ADMIT
  ηp-compat (Sl M) = ADMIT
  μp-compat (Sl M) = ADMIT
  unit-l (Sl M) = ADMIT
  unit-r (Sl M) = ADMIT
  assoc (Sl M) = ADMIT
  -----
  unit-l-ρ (Sl M)= ADMIT
