{-# OPTIONS --without-K #-}
module WTypes where

open import HoTT

open import Polynomial
open import PolyMisc

data W {ℓ} {I : Type ℓ} (P : Poly I I) : I → Type ℓ where
  leaf : (i : I) → W P i
  node : {i : I} → ⟦ P ⟧ (W P) i → W P i

module _ {ℓ} {I : Type ℓ} {P : Poly I I} where
  equiv-W : {i : I} → W P i ≃ (⊤ ⊔ ⟦ P ⟧ (W P) i)
  equiv-W {i} = unroll-W , is-eq unroll-W roll-W unroll-roll roll-unroll
    where
      unroll-W : {i : I} → W P i → ⊤ ⊔ ⟦ P ⟧ (W P) i
      unroll-W (leaf i) = inl unit
      unroll-W (node (c , φ)) = inr (c , φ)

      roll-W : {i : I} → ⊤ ⊔ ⟦ P ⟧ (W P) i → W P i
      roll-W {i} (inl _) = leaf i
      roll-W (inr (c , φ)) = node (c , φ)

      unroll-roll : ∀ {i} → (uw : ⊤ ⊔ ⟦ P ⟧ (W P) i) → unroll-W (roll-W uw) ==  uw
      unroll-roll (inl x) = idp
      unroll-roll (inr x) = idp

      roll-unroll : ∀ {i} → (w : W P i) → roll-W (unroll-W w) == w
      roll-unroll (leaf i) = idp
      roll-unroll (node x) = idp


  {-# TERMINATING #-}
  W-preserves-level : (γ-set : (i : I) → is-set (γ P i)) →
                      (i : I) → is-set (W P i)
  W-preserves-level γ-set i = equiv-preserves-level ((equiv-W {i}) ⁻¹)
    (⊔-level Unit-has-level (Σ-level (γ-set i) (λ c → Π-level (λ p → W-preserves-level γ-set (τ P p)))))

  -- ↓-W-leaf-in : {i₀ i₁ : I} {q : i₀ == i₁}
  --            → leaf i₀ == leaf i₁ [ W P ↓ q ]
  -- ↓-W-leaf-in {q = idp} = idp

  -- ↓-W-leaf-out : {i i′ : I} {q : i == i′}
  --             → leaf i == leaf i′ [ W P ↓ q ]
  --             → i == i′
  -- ↓-W-leaf-out {q = q} _ = q

  -- ↓-W-leaf-β : {i i′ : I} {q : i == i′} → (l : leaf i == leaf i′ [ W P ↓ q ])
  --           → (↓-W-leaf-out (↓-W-leaf-in {q = q})) == q
  -- ↓-W-leaf-β {q = idp} _ = idp

  -- ↓-W-leaf-η : {i i′ : I} {q : i == i′} → (l : leaf i == leaf i′ [ W P ↓ q ])
  --           → ↓-W-leaf-in {q = ↓-W-leaf-out l} == l
  -- ↓-W-leaf-η {i} {.i} {q = idp} l = ! (ap (<– lf=lf-equiv) contr-in-⊤) ∙ (<–-inv-l lf=lf-equiv l)
  --   -- TODO: take lf=lf-equiv and nd=nd-eqv out of where blocks
  --   where lf=lf-equiv : (leaf i == leaf i) ≃ (unit == unit)
  --         lf=lf-equiv = inl=inl-equiv unit unit ∘e equiv-ap equiv-W (leaf i) (leaf i)

  --         contr-in-⊤ : –> lf=lf-equiv l == idp
  --         contr-in-⊤ = fst $ ⊤-is-set unit unit (–> lf=lf-equiv l) idp

  ↓-W-node-in : {i i′ : I} {q : i == i′} {c : γ P i} {c′ : γ P i′}
                {φ : ⟦ P ⟧⟦ c ≺ W P ⟧ } {φ′ : ⟦ P ⟧⟦ c′ ≺ W P ⟧ }
                (r : c == c′ [ γ P ↓ q ])
                (s : φ == φ′ [ ⟦ P ⟧≺ (W P) ↓ pair= q r ])
             → node (c , φ) == node (c′ , φ′) [ W P ↓ q ]
  ↓-W-node-in {q = idp} idp s = ap (λ φ' → node (_ , φ')) s

  -- ↓-W-node-con : {i i′ : I} {q : i == i′} {c : γ P i} {c′ : γ P i′}
  --                {φ : ⟦ P ⟧⟦ c ≺ W P ⟧ } {φ′ : ⟦ P ⟧⟦ c′ ≺ W P ⟧ }
  --             → (node (c , φ) == node (c′ , φ′) [ W P ↓ q ])
  --             → c == c′ [ γ P ↓ q ]
  -- ↓-W-node-con {i} {q = idp} {c} {c′} {φ} {φ′} n=n = fst= cφ=c′φ′
  --     where nd=nd-eqv : (node (c , φ) == node (c′ , φ′)) ≃ ((c , φ) == (c′ , φ′))
  --           nd=nd-eqv = inr=inr-equiv (c , φ) (c′ , φ′) ∘e equiv-ap equiv-W (node (c , φ)) (node (c′ , φ′))

  --           cφ=c′φ′ : (c , φ) == (c′ , φ′)
  --           cφ=c′φ′ = –> nd=nd-eqv n=n

  -- ↓-W-node-dec : {i i′ : I} {q : i == i′} {c : γ P i} {c′ : γ P i′}
  --                {φ : ⟦ P ⟧⟦ c ≺ W P ⟧ } {φ′ : ⟦ P ⟧⟦ c′ ≺ W P ⟧ }
  --                → (r : (node (c , φ) == node (c′ , φ′) [ W P ↓ q ]))
  --                → φ == φ′ [ ⟦ P ⟧≺ (W P) ↓ pair= q (↓-W-node-con r) ]
  -- ↓-W-node-dec {i} {q = idp} {c} {c′} {φ} {φ′} r = φ=φ′
  --   where nd=nd-eqv : (node (c , φ) == node (c′ , φ′)) ≃ ((c , φ) == (c′ , φ′))
  --         nd=nd-eqv = inr=inr-equiv (c , φ) (c′ , φ′) ∘e equiv-ap equiv-W (node (c , φ)) (node (c′ , φ′))

  --         cφ=c′φ′ : (c , φ) == (c′ , φ′)
  --         cφ=c′φ′ = –> nd=nd-eqv r

  --         φ=φ′ : φ == φ′ [ ⟦ P ⟧≺ (W P) ↓ pair= idp (fst= cφ=c′φ′) ]
  --         φ=φ′ = ↓-Σ-snd cφ=c′φ′

  ↓-W-node-lcl-in : {i : I} {c : γ P i} {φ φ′ : ⟦ P ⟧⟦ c ≺ W P ⟧}
                    (s : (p : ρ P c) → φ p == φ′ p)
                    → node (c , φ) == node (c , φ′)
  ↓-W-node-lcl-in s = ↓-W-node-in idp (λ= s)

  -- ↓-W-node-lcl-out : {i : I} {c : γ P i} {φ φ′ : ⟦ P ⟧⟦ c ≺ W P ⟧}
  --                 → (q : node (c , φ) == node (c , φ′))
  --                 → =Σ {A = γ P i} {B = λ c → ⟦ P ⟧⟦ c ≺ W P ⟧} (c , φ) (c , φ′)
  -- ↓-W-node-lcl-out {i} {c} {φ} {φ′} q = fst= cφ=cφ′ , snd= cφ=cφ′
  --   where nd=nd-eqv : (node (c , φ) == node (c , φ′)) ≃ ((c , φ) == (c , φ′))
  --         nd=nd-eqv = inr=inr-equiv (c , φ) (c , φ′) ∘e equiv-ap equiv-W (node (c , φ)) (node (c , φ′))

  --         cφ=cφ′ : (c , φ) == (c , φ′)
  --         cφ=cφ′ = –> nd=nd-eqv q

  -- ↓-W-node-lcl-in′ : {i : I} {c : γ P i} {q : c == c} {φ φ′ : ⟦ P ⟧⟦ c ≺ W P ⟧}
  --                   (s : φ == φ′ [ ⟦ P ⟧≺ (W P) ↓ pair= idp q ])
  --                → node (c , φ) == node (c , φ′)
  -- ↓-W-node-lcl-in′ {q = q} s = ↓-W-node-in q s

--  ↓-W-node-lcl-β : {i : I} {c : γ P i} {q : c == c} {φ φ′ : ⟦ P ⟧⟦ c ≺ W P ⟧}
--                   (s : φ == φ′ [ ⟦ P ⟧≺ (W P) ↓ pair= idp q ])
--                → ↓-W-node-lcl-out (↓-W-node-lcl-in′ s) == q , {!!}
--  ↓-W-node-lcl-β {i} {c} {φ} {φ′} s = {!!}
--    ↓-W-node-lcl-out (↓-W-node-lcl-in s) =⟨ idp |in-ctx (λ x → ↓-W-node-lcl-out x) ⟩
--    ↓-W-node-lcl-out (↓-W-node-in idp (λ= s)) =⟨ idp |in-ctx (λ x → ↓-W-node-lcl-out x) ⟩
--    ↓-W-node-lcl-out (ap (λ x → node (c , x)) (λ= s)) =⟨ {!!} ⟩
--    idp , {!!} =⟨ {!!} ⟩
--    {!!} , λ= s ∎

module _ {ℓ} {I : Type ℓ} {P : Poly I I} where

  leafOf : {i : I} → W P i → Type ℓ
  leafOf (leaf i) = Lift Unit
  leafOf (node (c , φ)) = Σ (ρ P c) (λ p → leafOf (φ p))

  leafOf′ : Σ I (W P) → Type ℓ
  leafOf′ (i , w) = leafOf w

  -- leafDec : {i : I} → (w : W P i) → has-dec-eq (leafOf w)
  -- leafDec (leaf i) = Lift-Unit-has-dec-eq
  -- leafDec (node (c , φ)) = Σ-has-dec-eq (ρ-dec P c) (λ p → leafDec (φ p))

  leafType : {i : I} → {w : W P i} → leafOf w → I
  leafType {w = leaf i} (lift unit) = i
  leafType {w = node _} (_ , l) = leafType l

  -- ↓-leaf-in : {i i′ : I} {i=i′ : i == i′}
  --             {c : γ P i} {c′ : γ P i′} (c=c′ : c == c′ [ γ P ↓ i=i′ ])
  --             {p : ρ P c} {p′ : ρ P c′} (p=p′ : p == p′ [ ρ-Σ P ↓ pair= i=i′ c=c′ ])
  --             {φ : ⟦ P ⟧⟦ c ≺ W P ⟧} {φ′ : ⟦ P ⟧⟦ c′ ≺ W P ⟧}
  --             → (φ=φ′ : φ == φ′ [ ⟦ P ⟧≺ (W P) ↓ pair= i=i′ c=c′ ])
  --             {lf : leafOf (φ p)} {lf′ : leafOf (φ′ p′)}
  --             → (lf=lf′ : lf == lf′ [ leafOf′ ↓ pair= (τ-inv P c=c′ p=p′) (↓-≺-out P φ=φ′ p=p′) ])
  --             → (p , lf) == (p′ , lf′) [ leafOf′ ↓ pair= i=i′ (↓-W-node-in c=c′ φ=φ′) ]
  -- ↓-leaf-in {i=i′ = idp} idp idp idp idp = idp

  -- ↓-leaf-lcl-in : {i : I} {c : γ P i} {p : ρ P c} {φ φ′ : ⟦ P ⟧⟦ c ≺ W P ⟧}
  --                 (s : (p : ρ P c) → φ p == φ′ p)
  --                 {l : leafOf (φ p)} {l′ : leafOf (φ′ p)} (t : l == l′ [ leafOf ↓ s p ])
  --                 → (p , l) == (p , l′) [ leafOf ↓ ↓-W-node-lcl-in s ]
  -- ↓-leaf-lcl-in {i} {c} {p} s {l} {l′} t = ↓-ap-out leafOf′ (_,_ i) (↓-W-node-lcl-in s) po₂
  --   where po₀ : l == l′ [ leafOf′ ↓ ap (_,_ (τ P p)) (s p) ]
  --         po₀ = ↓-ap-in leafOf′ (λ w → (τ P p) , w) t

  --         po₁ : l == l′ [ leafOf′ ↓ ap (_,_ (τ P p)) (↓-≺-out P {X = W P} (λ= s) idp) ]
  --         po₁ = transport (λ x → l == l′ [ leafOf′ ↓ ap (_,_ (τ P p)) x ]) (! (app=-β s p)) po₀

  --         po₂ : (p , l) == (p , l′) [ leafOf′ ↓ (ap (_,_ i) (↓-W-node-lcl-in s)) ]
  --         po₂ = ↓-leaf-in idp idp (λ= s) po₁

--  ↓-leaf-lcl-in′ : {i : I} {c : γ P i} {p : ρ P c} {φ φ′ : ⟦ P ⟧⟦ c ≺ W P ⟧}
--                  (s : (p : ρ P c) → φ p == φ′ p)
--                  {l : leafOf (φ p)} {l′ : leafOf (φ′ p)} (t : l == l′ [ leafOf ↓ s p ])
--                  → (p , l) == (p , l′) [ leafOf ↓ ↓-W-node-lcl-in s ]
--  ↓-leaf-lcl-in′ {i} {c} {p} s {l} {l′} t = ↓-Σ-in {A = ρ P c} {C = λ q w →  } {!!} {!!} {!!}


   -- We need one more for the type coherence, but I don't quite see what we're doing here ....
--   -- ↓-leaf-type-lcl-in : {i : I} {c : γ P i} {p : ρ P c} {φ₀ φ₁ : ⟦ P ⟧⟦ c ≺ W P ⟧}
--   --                      (s : (p' : ρ P c) → φ₀ p' == φ₁ p')
--   --                      {l₀ : leafOf (φ₀ p)} {l₁ : leafOf (φ₁ p)}
--   --                      (t : l₀ == l₁ [ leafOf ↓ s p ]) →
--   --                      {!!} == {!!} [ (λ wl → {!leafType!} == leafType (snd wl)) ↓ pair= (↓-W-node-lcl-in s) (↓-leaf-lcl-in s t) ]
--   -- ↓-leaf-type-lcl-in s t = {!!}

  nodeOf : {i : I} → W P i → Type ℓ
  nodeOf (leaf i) = Lift Empty
  nodeOf (node (c , φ)) = Lift {j = ℓ} Unit ⊔ (Σ (ρ P c) (λ p → nodeOf (φ p)))

  -- nodeDec : {i : I} → (w : W P i) → has-dec-eq (nodeOf w)
  -- nodeDec (leaf i) (lift ())
  -- nodeDec (node (c , φ)) = ⊔-has-dec-eq Lift-Unit-has-dec-eq (Σ-has-dec-eq (ρ-dec P c) (λ p → nodeDec (φ p)))

  nodeType : {i : I} → {w : W P i} → nodeOf w → Σ I (γ P)
  nodeType {w = leaf ._} (lift ())
  nodeType {w = node (c , _)} (inl _) = (_ , c)
  nodeType {w = node _} (inr (_ , n)) = nodeType n

--   nodeOutType : {i : I} → {w : W P i} → nodeOf w → I
--   nodeOutType {w = leaf ._} (lift e) = ⊥-rec e
--   nodeOutType {i} {w = node (c , φ)} (inl _) = i
--   nodeOutType {i} {w = node (c , φ)} (inr (p , n)) = nodeOutType n

  -- nodeTrans : {i₀ i₁ : I} {q : i₀ == i₁ } {w₀ : W P i₀} {w₁ : W P i₁} →
  --             w₀ == w₁ [ W P ↓ q ] → nodeOf w₀ → nodeOf w₁
  -- nodeTrans {q = idp} idp n = n

  -- nodeTypeCoh : {i₀ i₁ : I} {q : i₀ == i₁ } {w₀ : W P i₀} {w₁ : W P i₁} →
  --               (e : w₀ == w₁ [ W P ↓ q ]) → (n : nodeOf w₀) →
  --               nodeType n == nodeType (nodeTrans e n)
  -- nodeTypeCoh {q = idp} idp n = idp

  corolla : {i : I} → (c : γ P i) → W P i
  corolla c = node (c , λ p → leaf _)

  -- corolla-node-unique : {i : I} {c : γ P i} → Lift {j = ℓ} Unit ≃ nodeOf (corolla c)
  -- corolla-node-unique =
  --   equiv (cst (inl lt)) (cst lt)
  --         (λ { (inl _) → idp ;
  --              (inr (_ , lift e)) → ⊥-rec e })
  --         (cst idp)
