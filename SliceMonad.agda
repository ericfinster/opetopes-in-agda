{-# OPTIONS --without-K #-}

open import HoTT

open import Polynomial
open import CartesianMorphism
open import PolynomialMonad
open import PolyMisc

module SliceMonad where

  module _ {ℓ} {I : Type ℓ} (M : PolyMonad I) where

    open PolyMonad 

    data SlCn : {i : I} → γ (P M) i → Type ℓ where
      dot : (i : I) → SlCn {i = i} (⟪ η M ⟫ lt)
      box : {i : I} → (c : γ (P M) i) → 
            (ε : (p : ρ (P M) c) → Σ (γ (P M) (τ (P M) p)) SlCn) → 
            SlCn (⟪ μ M ⟫ (c , fst ∘ ε))
  
    SlPl : {i : I} → {c : γ (P M) i} → (w : SlCn c) → Type ℓ
    SlPl (dot i) = Lift ⊥
    SlPl (box c ε) = Lift {j = ℓ} ⊤ ⊔ Σ (ρ (P M) c) (λ p → SlPl (snd (ε p)))

    B : Type ℓ
    B = Σ I (γ (P M))

    {-# TERMINATING #-}
    SlP : Poly B B
    γ SlP (i , c) = SlCn c
    ρ SlP {i , c} n = SlPl n
    τ SlP {i , _} {dot .i} (lift ())
    τ SlP {i , _} {box c ε} (inl (lift unit)) = i , c
    τ SlP {i , _} {box c ε} (inr (p , n)) = τ SlP n

    sl-η : IdP B ⇝ SlP
    γ-map sl-η {i , c} _ = transport SlCn (γ≈ (η-left-law M c)) (box c (λ p → (⟪ η M ⟫ lt) , dot (τ (P M) p)))
    ρ-eqv sl-η {i , c} {lift unit} = {!!} ∘e lemma 

      where lemma : Lift {j = ℓ} ⊤ ≃ SlPl (box c (λ p → ⟪ η M ⟫ lt , dot (τ (P M) p)))
            lemma = (λ { (lift unit) → inl lt }) , is-eq _ (λ { p → lt }) 
                    (λ { (inl (lift unit)) → idp ; (inr (_ , lift ())) }) 
                    (λ { (lift unit) → idp })

    τ-coh sl-η p = {!!}

    -- open ADMIT

    -- {-# TERMINATING #-}
    -- sl-join : {b : B} → γ (SlP ⊚ SlP) b → γ SlP b
    -- sl-join {i , ._} ((leaf .i , idp) , ψ) = ⟪ sl-η ⟫ lt
    -- sl-join {i , ._} ((node (c , φ) , idp) , ψ) = 
    --   (⟪ fr-μ (P M) ⟫ (localTree , fst ∘ IH) , ADMIT)  -- ! (γ≈ (ε-is-monad-map (localTree , fst ∘ IH))) ∙ {!!})

    --   where localCons : γ SlP (i , c)
    --         localCons = ψ (inl lt)

    --         localTree : W (P M) i
    --         localTree = fst localCons

    --         localEv : ⟪ ε ⟫ localTree == c
    --         localEv = snd localCons
  
    --         liftDec : ⟦ FrP (P M) ⟧⟦ localTree ≺ W (P M) ⟧
    --         liftDec = ⟪ ε ∣ W (P M) ↓ localEv ⟫⇑ φ

    --         nextTree : (l : leafOf localTree) → W (P M) (leafType l)
    --         nextTree l = liftDec l

    --         nextCons : (l : leafOf localTree) → γ (P M) (leafType l)
    --         nextCons l = ⟪ ε ⟫ (nextTree l)

    --         nodeCoe : (l : leafOf localTree) → (n : nodeOf (nextTree l)) → nodeOf (node (c , φ))
    --         nodeCoe l n = inr (⟦ P M ↓ localEv ⟧↓ ( ⟪ ε ⟫↓ l) , nodeTrans (⟪ ε ∣ W (P M) ↓ localEv ⟫⇑-po φ l) n)

    --         nodeCoh : (l : leafOf localTree) → (n : nodeOf (nextTree l)) → nodeType n == nodeType (nodeCoe l n)
    --         nodeCoh l n = nodeTypeCoh (⟪ ε ∣ W (P M) ↓ localEv ⟫⇑-po φ l) n

    --         nextDec : (l : leafOf localTree) → ⟦ SlP ⟧⟦ nextTree l , idp ≺ γ SlP ⟧
    --         nextDec l n = transport (γ SlP)  (! (nodeCoh l n)) (ψ (nodeCoe l n)) 

    --         IH : (l : leafOf localTree) → γ SlP (leafType l , nextCons l)
    --         IH l = sl-join {leafType l , nextCons l} ((nextTree l , idp) , nextDec l)

    --         IH-ev : (l : leafOf localTree) → ⟪ ε ⟫ (fst (IH l)) == nextCons l
    --         IH-ev l = snd (IH l)

    --         -- unfold : ⟪ (ε ∥ ε) ▶ μ M ⟫ (localTree , fst ∘ IH) == 
    --         --          ⟪ (ε ∥ ε) ▶ μ M ⟫ (localTree , fst ∘ IH) 
    --         -- unfold = ⟪ μ M ⟫ (⟪ ε ⟫ localTree , (λ p → transport (γ (P M)) (⟪ ε ⓐ localTree ⟫↑= p) (⟪ ε ⟫ ((fst ∘ IH) (⟪ ε ⟫↑ p))))) =⟨ idp ⟩ 
    --         --          ⟪ (ε ∥ ε) ▶ μ M ⟫ (localTree , fst ∘ IH) ∎

    --         -- goal : ⟪ ε ⟫ (⟪ fr-μ (P M) ⟫ (localTree , fst ∘ IH)) == ⟪ ε ⟫ (node (c , φ))
    --         -- goal = ⟪ ε ⟫ (⟪ fr-μ (P M) ⟫ (localTree , fst ∘ IH)) =⟨ ! (γ≈ (ε-is-monad-map (localTree , fst ∘ IH))) ⟩
    --         --        ⟪ (ε ∥ ε) ▶ μ M ⟫ (localTree , fst ∘ IH) =⟨ {!ADMIT!} ⟩ 
                   
    --         --        ⟪ ε ⟫ (node (c , φ)) ∎

    -- sl-μ : SlP ⊚ SlP ⇝ SlP
    -- γ-map sl-μ = sl-join
    -- ρ-eqv sl-μ = ADMIT
    -- τ-coh sl-μ = ADMIT
   
    -- SlM : PolyMonad B
    -- P SlM = SlP
    -- η SlM = sl-η
    -- μ SlM = sl-μ
    -- η-left-law SlM c = ADMIT
    -- η-right-law SlM c = ADMIT
    -- μ-assoc-law SlM c = ADMIT

