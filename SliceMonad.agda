{-# OPTIONS --without-K #-}

open import HoTT

open import Polynomial
open import CartesianMorphism
open import PolynomialMonad
open import PolyMisc

module SliceMonad where

  module _ {ℓ} {I : Type ℓ} (M : PolyMonad I) where

    open PolyMonad 
    open ADMIT

    data SlCn : {i : I} → γ (P M) i → Type ℓ where
      dot : (i : I) → SlCn {i = i} (⟪ η M ⟫ lt)
      box : {i : I} → (c : γ (P M) i) → 
            (δ : (p : ρ (P M) c) → γ (P M) (τ (P M) p)) → 
            (ε : (p : ρ (P M) c) → SlCn (δ p)) → 
            SlCn (⟪ μ M ⟫ (c , δ))
  
    SlPl : {i : I} → {c : γ (P M) i} → (w : SlCn c) → Type ℓ
    SlPl (dot i) = Lift ⊥
    SlPl (box c δ ε) = Lift {j = ℓ} ⊤ ⊔ Σ (ρ (P M) c) (λ p → SlPl (ε p))

    B : Type ℓ
    B = Σ I (γ (P M))

    SlCn' : B → Type ℓ
    SlCn' (i , c) = SlCn c
    
    {-# TERMINATING #-}
    SlP : Poly B B
    γ SlP (i , c) = SlCn c
    ρ SlP {i , c} n = SlPl n
    τ SlP {i , _} {dot .i} (lift ())
    τ SlP {i , _} {box c δ ε} (inl (lift unit)) = i , c
    τ SlP {i , _} {box c δ ε} (inr (p , n)) = τ SlP n

    sl-η : IdP B ⇝ SlP
    γ-map sl-η {i , c} _ = transport SlCn (γ≈ (η-left-law M c)) (box c (λ p → ⟪ η M ⟫ lt) (λ p → dot (τ (P M) p)))
    ρ-eqv sl-η {i , c} {lift unit} = {!!} ∘e lemma 

       where lemma : Lift {j = ℓ} ⊤ ≃ SlPl (box c (λ p → ⟪ η M ⟫ lt) (λ p → dot (τ (P M) p)))
             lemma = (λ { (lift unit) → inl lt }) , is-eq _ (λ { p → lt }) 
                     (λ { (inl (lift unit)) → idp ; (inr (_ , lift ())) }) 
                     (λ { (lift unit) → idp })

    τ-coh sl-η p = {!!}

    sl-graft : {i : I} → {c : γ (P M) i} → (w : SlCn c) → 
               (δ : (p : ρ (P M) c) → γ (P M) (τ (P M) p)) →
               (ε : (p : ρ (P M) c) → SlCn (δ p)) → SlCn (⟪ μ M ⟫ (c , δ)) 
    sl-graft (dot i) δ₁ ε₁ = transport! SlCn' (pair= (τ-coh (η M) lt) {!!}) (ε₁ (⟪ η M ⟫↓ lt)) 
    sl-graft (box c δ ε) δ₁ ε₁ = transport! SlCn {!!} (box c (λ p → ⟪ μ M ⟫ (δ p , α p)) IH)
    
      where α : (p : ρ (P M) c) → (q : ρ (P M) (δ p)) → γ (P M) (τ (P M) q)
            α p q = {!!}

            β : (p : ρ (P M) c) → (q : ρ (P M) (δ p)) → SlCn (α p q)
            β p q = {!!}
            
            IH : (p : ρ (P M) c) → SlCn (⟪ μ M ⟫ (δ p , α p))
            IH p = sl-graft (ε p) (α p) (β p)
            
    {-# TERMINATING #-}
    sl-μ : SlP ⊚ SlP ⇝ SlP
    γ-map sl-μ (dot i , κ) = dot i
    γ-map sl-μ (box {i} c δ ε , κ) = sl-graft (κ (inl lt)) δ (λ p → γ-map sl-μ (ε p , (λ q → κ (inr (p , q)))))
    ρ-eqv sl-μ = {!!}
    τ-coh sl-μ p = {!!}

  -- μ (Slice M) (dot i) δ = dot i
  -- μ (Slice M) (box c ε) κ = SlGrft M (κ (inl tt)) (λ p → fst (ε p) , μ (Slice M) (snd (ε p)) (λ q → κ (inr (p , q))))
