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
    SlGrftPl₀ (box c δ ε) δ₁ ε₁ (inr (p , n)) = trans-lemma SlCn SlPl (assoc c δ δ₁) _ (inr (p , SlGrftPl₀ (ε p) (δ₁' p) (ε₁' p) n)) 
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
