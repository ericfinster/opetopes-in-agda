{-# OPTIONS --without-K #-}

open import HoTT

open import Polynomial
open import PolyMisc

module WTypes where

  data W {i} {I : Type i} (P : Poly I I) : I → Set i where
    leaf : (i : I) → W P i
    node : {i : I} → ⟦ P ⟧ (W P) i → W P i

  module _ {ℓ} {I : Type ℓ} {P : Poly I I} where

    ↓-W-leaf-in : {i₀ i₁ : I} {q : i₀ == i₁} → 
             (leaf i₀) == (leaf i₁) [ (W P) ↓ q ]
    ↓-W-leaf-in {q = idp} = idp

    ↓-W-node-in : {i₀ i₁ : I} {q : i₀ == i₁} {c₀ : γ P i₀} {c₁ : γ P i₁}
                  {φ₀ : ⟦ P ⟧⟦ c₀ ≺ W P ⟧ } {φ₁ : ⟦ P ⟧⟦ c₁ ≺ W P ⟧ } → 
                  (r : c₀ == c₁ [ γ P ↓ q ]) → 
                  (s : φ₀ == φ₁ [ ⟦ P ⟧≺ (W P) ↓ pair= q r ]) → 
                  (node (c₀ , φ₀)) == (node (c₁ , φ₁)) [ (W P) ↓ q ]
    ↓-W-node-in {q = idp} idp s = ap (λ φ' → node (_ , φ')) s 

    ↓-W-node-lcl-in : {i : I} {c : γ P i} {φ₀ φ₁ : ⟦ P ⟧⟦ c ≺ W P ⟧} → 
                      (s : (p : ρ P c) → φ₀ p == φ₁ p) → 
                      node (c , φ₀) == node (c , φ₁)
    ↓-W-node-lcl-in s = ↓-W-node-in idp (λ= s)

    -- W-unroll : (i : I) → W P i ≃ (⊤ ⊔ ⟦ P ⟧ (W P) i)
    -- W-unroll = {!!}

  module _ {ℓ} {I : Type ℓ} {P : Poly I I} where

    leafOf : {i : I} → W P i → Type ℓ
    leafOf (leaf i) = Lift Unit
    leafOf (node (c , φ)) = Σ (ρ P c) (λ p → leafOf (φ p)) 
      
    leafOf' : Σ I (W P) → Type ℓ
    leafOf' (i , w) = leafOf w

    -- leafDec : {i : I} → (w : W P i) → has-dec-eq (leafOf w)
    -- leafDec (leaf i) = Lift-Unit-has-dec-eq
    -- leafDec (node (c , φ)) = Σ-has-dec-eq (ρ-dec P c) (λ p → leafDec (φ p))

    leafType : {i : I} → {w : W P i} → leafOf w → I
    leafType {w = leaf i} (lift unit) = i
    leafType {w = node _} (_ , l) = leafType l

  --   ↓-leaf-in : {i₀ i₁ : I} {q : i₀ == i₁}
  --               {c₀ : γ P i₀} {c₁ : γ P i₁} (r : c₀ == c₁ [ γ P ↓ q ])
  --               {p₀ : ρ P c₀} {p₁ : ρ P c₁} (s : p₀ == p₁ [ ρ' P ↓ pair= q r ])
  --               {φ₀ : ⟦ P ⟧⟦ c₀ ≺ W P ⟧} {φ₁ : ⟦ P ⟧⟦ c₁ ≺ W P ⟧}
  --               (t : φ₀ == φ₁ [ ⟦ P ⟧≺ (W P) ↓ pair= q r ]) 
  --               {l₀ : leafOf (φ₀ p₀)} {l₁ : leafOf (φ₁ p₁)} 
  --               (u : l₀ == l₁ [ leafOf' ↓ pair= (τ-inv P {q = q} s) (↓-≺-out P t p₀ p₁ s) ]) → 
  --               (p₀ , l₀) == (p₁ , l₁) [ leafOf' ↓ pair= q (↓-W-node-in r t) ]
  --   ↓-leaf-in {q = idp} idp idp idp idp = idp

  --   -- Maybe you can clean this up a bit ...
  --   ↓-leaf-lcl-in : {i : I} {c : γ P i} {p : ρ P c} {φ₀ φ₁ : ⟦ P ⟧⟦ c ≺ W P ⟧}
  --                   (s : (p' : ρ P c) → φ₀ p' == φ₁ p')
  --                   {l₀ : leafOf (φ₀ p)} {l₁ : leafOf (φ₁ p)}
  --                   (t : l₀ == l₁ [ leafOf ↓ s p ]) → 
  --                   (p , l₀) == (p , l₁) [ leafOf ↓ ↓-W-node-lcl-in s ]
  --   ↓-leaf-lcl-in {i} {c} {p} s {l₀ = l₀} {l₁ = l₁} t = ↓-ap-out leafOf' (_,_ i) (↓-W-node-lcl-in s) po₂

  --     where po₀ : l₀ == l₁ [ leafOf' ↓ ap (_,_ (τ P p)) (s p) ]
  --           po₀ = ↓-ap-in leafOf' (λ w → (τ P p) , w) t

  --           po₁ : l₀ == l₁ [ leafOf' ↓ ap (_,_ (τ P p)) (↓-≺-out P {X = W P} (λ= s) p p idp) ]
  --           po₁ = transport (λ x → l₀ == l₁ [ leafOf' ↓ ap (_,_ (τ P p)) x ]) (! (app=-β s p)) po₀

  --           po₂ : (p , l₀) == (p , l₁) [ leafOf' ↓ (ap (_,_ i) (↓-W-node-lcl-in s)) ]
  --           po₂ = ↓-leaf-in idp idp (λ= s) po₁

  --   -- We need one more for the type coherence, but I don't quite see what we're doing here ....

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

    nodeTrans : {i₀ i₁ : I} {q : i₀ == i₁ } {w₀ : W P i₀} {w₁ : W P i₁} → 
                w₀ == w₁ [ W P ↓ q ] → nodeOf w₀ → nodeOf w₁
    nodeTrans {q = idp} idp n = n

    nodeTypeCoh : {i₀ i₁ : I} {q : i₀ == i₁ } {w₀ : W P i₀} {w₁ : W P i₁} → 
                  (e : w₀ == w₁ [ W P ↓ q ]) → (n : nodeOf w₀) → 
                  nodeType n == nodeType (nodeTrans e n)
    nodeTypeCoh {q = idp} idp n = idp

    corolla : {i : I} → (c : γ P i) → W P i
    corolla c = node (c , λ p → leaf _)

    corolla-node-unique : {i : I} {c : γ P i} → Lift {j = ℓ} Unit ≃ nodeOf (corolla c)
    corolla-node-unique = 
      equiv (cst (inl lt)) (cst lt) 
            (λ { (inl _) → idp ; 
                 (inr (_ , lift e)) → ⊥-rec e }) 
            (cst idp)

