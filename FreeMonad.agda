--
--  FreeMonad.agda - The free monad on a polynomial
--
--  Eric Finster
--

open import Prelude
open import Polynomial
open import PolynomialMonad

module FreeMonad where

  module FreeM (I : Set) (P : Poly I I) where
    
    open Poly
    open _≃_

    FrP : Poly I I
    FrP = record { 
            γ = W P ; 
            ρ = λ { (i , w) → leafOf w } ; 
            τ = λ { ((i , w) , l) → leafType l } 
          }

    fr-η : IdP I ⇛ FrP
    fr-η = record { 
             γ-map = λ i c → leaf i ; 
             ρ-eqv = λ i c → id-equiv ⊤ ;
             τ-coh = λ i c p → idp
           }

    {-# TERMINATING #-}
    fr-graft : (i : I) → γ (FrP ⊚ FrP) i → γ FrP i
    fr-graft i (leaf .i , ψ) = ψ tt
    fr-graft i (node .i (c , φ) , ψ) = 
      node i (c , (λ p₀ → fr-graft (τ P ((i , c) , p₀)) (φ p₀ , (λ p₁ → ψ (p₀ , p₁)))))

    {-# TERMINATING #-}
    fr-place-eqv : (i : I) (c : γ (FrP ⊚ FrP) i) → ρ (FrP ⊚ FrP) (i , c) ≃ ρ FrP (i , fr-graft i c)
    fr-place-eqv i (leaf .i , ψ) = Σ-eqv-base (ρ FrP (i , (ψ tt)))
    fr-place-eqv i (node .i (c , φ) , ψ) = 
      Σ-eqv-inv (ρ P (i , c)) _ _ (λ p → fr-place-eqv (τ P ((i , c) , p)) (φ p , (λ p₀ → ψ (p , p₀)))) ⊙ (Σ-eqv-lift _ _ _)

    {-# TERMINATING #-}
    fr-type-coh : (i : I) (c : γ (FrP ⊚ FrP) i) (p : ρ (FrP ⊚ FrP) (i , c)) →
                  τ (FrP ⊚ FrP) ((i , c) , p) ==
                  τ FrP ((i , fr-graft i c) , f (fr-place-eqv i c) p)
    fr-type-coh i (leaf .i , ψ) (p₀ , p₁) = idp
    fr-type-coh i (node .i (c , φ) , ψ) ((p , l₀) , l₁) = 
      leafType l₁ =⟨ fr-type-coh (τ P ((i , c) , p)) (φ p , (λ p₀ → ψ (p , p₀))) (l₀ , l₁)  ⟩ 
      leafType (f (fr-place-eqv (τ P ((i , c) , p)) (φ p , (λ p₀ → ψ (p , p₀)))) (l₀ , l₁)) ∎
  
    fr-μ : FrP ⊚ FrP ⇛ FrP
    fr-μ = record { 
             γ-map = fr-graft ; 
             ρ-eqv = fr-place-eqv ; 
             τ-coh = fr-type-coh 
           }

    open UnitLemmas FrP fr-η
    open AssocLemmas FrP fr-μ

    fr-unit-leaf-law : {i : I} (c : γ FrP i) → mult (unit-leaf-decor c) == c
    fr-unit-leaf-law (leaf i) = idp
    fr-unit-leaf-law (node i (c , φ)) = ap (λ φ₀ → node i (c , φ₀)) (funext IH)

      where IH : (p : ρ P (_ , c)) → mult (unit-leaf-decor (φ p)) == φ p
            IH p = fr-unit-leaf-law (φ p)

    fr-unit-root-law : {i : I} (c : γ FrP i) → mult (unit-root-decor c) == c
    fr-unit-root-law (leaf i) = idp
    fr-unit-root-law (node i (c , φ)) = idp

    module _ {i : I} {c : γ P i}
      (φ : (p : ρ P (i , c)) → W P (τ P (_ , p)))
      (ψ : (p : leafOf (node i (c , φ))) → γ (FrP ⊚ FrP) (τ FrP (_ , p)))
      (p₀ : ρ P (_ , c)) (l : leafOf (mult (φ p₀ , (λ p₁ → proj₁ (ψ (p₀ , p₁)))))) where

      d : γ (FrP ⊚ FrP) _
      d = (φ p₀ , (λ p₁ → proj₁ (ψ (p₀ , p₁))))
        
      -- Anyone?
      postulate
        main-lemma : transport (W P) (lift-place-coh {d = d} l) (proj₂ (ψ (p₀ , proj₁ (lift-place l))) (proj₂ (lift-place {d = d} l))) == 
                     induced-decor (proj₂ (decor-assoc-right i (_ , ψ))) (p₀ , l) 


    {-# TERMINATING #-}
    fr-assoc-law : {i : I} (c : γ (FrP ⊚ FrP ⊚ FrP) i) →
                   mult (mult-left c) == mult (mult-right (decor-assoc-right i c))
    fr-assoc-law (leaf i , ψ) = idp
    fr-assoc-law (node i (c , φ) , ψ) =
      mult (mult-left (node i (c , φ) , ψ))                                                                                                        =⟨ idp ⟩ 
      mult (node i (c , φ) , λ p → mult (ψ p))                                                                                                     =⟨ idp ⟩ 
      node i (c , λ p₀ → mult (φ p₀ , λ p₁ → mult (ψ (p₀ , p₁))))                                                                                  =⟨ idp ⟩
      node i (c , λ p₀ → mult (mult-left (φ p₀ , (λ p₁ → ψ (p₀ , p₁)))))                                                                           =⟨ funext IH |in-ctx (λ φ₀ → node i (c , φ₀)) ⟩ 
      node i (c , λ p₀ → mult (mult-right (decor-assoc-right _ (φ p₀ , (λ p₁ → ψ (p₀ , p₁))))))                                                    =⟨ idp ⟩ 
      node i (c , λ p₀ → mult (mult-right ((φ p₀ , (λ p₁ → proj₁ (ψ (p₀ , p₁)))) , (λ { (p₁ , p₂) → proj₂ (ψ (p₀ , p₁)) p₂ }))))                   =⟨ idp ⟩ 
      node i (c , λ p₀ → mult (mult (φ p₀ , (λ p₁ → proj₁ (ψ (p₀ , p₁)))) , induced-decor (λ { (p₁ , p₂) → proj₂ (ψ (p₀ , p₁)) p₂ })))             =⟨ funext lemma₀ |in-ctx (λ φ₀ → node i (c , φ₀))⟩ 
      node i (c , λ p₀ → mult (mult (φ p₀ , (λ p₁ → proj₁ (ψ (p₀ , p₁)))) , ((λ q → (induced-decor (λ { (p₀ , p₁) → proj₂ (ψ p₀) p₁ })) (p₀ , q))) )) =⟨ idp ⟩ 
      mult (node i (c , λ p₀ → mult (φ p₀ , (λ p₁ → proj₁ (ψ (p₀ , p₁))))) , induced-decor (λ { (p₀ , p₁) → proj₂ (ψ p₀) p₁ }))                       =⟨ idp ⟩ 
      mult (mult (node i (c , φ) , (λ p → proj₁ (ψ p))) , induced-decor (λ { (p₀ , p₁) → proj₂ (ψ p₀) p₁ }))                                          =⟨ idp ⟩ 
      mult (mult-right ((node i (c , φ) , (λ p → proj₁ (ψ p))) , (λ { (p₀ , p₁) → proj₂ (ψ p₀) p₁ }) ))                                             =⟨ idp ⟩ 
      mult (mult-right (decor-assoc-right i (node i (c , φ) , ψ))) ∎

      where IH : (p : ρ P (i , c)) → mult (mult-left (φ p , (λ p₁ → ψ (p , p₁)))) == 
                                     mult (mult-right (decor-assoc-right (τ P ((i , c) , p)) (φ p , (λ p₁ → ψ (p , p₁)))))
            IH p = fr-assoc-law (φ p , (λ p₁ → ψ (p , p₁)))

            lemma : (p₀ : ρ P (i , c)) → induced-decor (λ { (p₁ , p₂) → proj₂ (ψ (p₀ , p₁)) p₂ }) == 
                                         (λ q → (induced-decor (λ { (p₀ , p₁) → proj₂ (ψ p₀) p₁ })) (p₀ , q))
            lemma p₀ = 
              induced-decor (λ { (p₁ , p₂) → proj₂ (ψ (p₀ , p₁)) p₂ }) =⟨ funext (main-lemma φ ψ p₀) ⟩ 
              (λ q → (induced-decor (λ { (p₀ , p₁) → proj₂ (ψ p₀) p₁ })) (p₀ , q)) ∎

            lemma₀ : (p₀ : ρ P (i , c)) → mult (mult (φ p₀ , (λ p₁ → proj₁ (ψ (p₀ , p₁)))) , induced-decor (λ { (p₁ , p₂) → proj₂ (ψ (p₀ , p₁)) p₂ })) ==
                                          mult (mult (φ p₀ , (λ p₁ → proj₁ (ψ (p₀ , p₁)))) , ((λ q → (induced-decor (λ { (p₀ , p₁) → proj₂ (ψ p₀) p₁ })) (p₀ , q))))
            lemma₀ p₀ = ap (λ X → mult (mult (φ p₀ , (λ p₁ → proj₁ (ψ (p₀ , p₁)))) , X)) (lemma p₀) 

    FrM : PolyMonad I
    FrM = record { 
            P = FrP ;
            η = fr-η ;
            μ = fr-μ ;
            unit-leaf-law = fr-unit-leaf-law ;
            unit-root-law = fr-unit-root-law ;
            assoc-law = fr-assoc-law
           }

  module _ where

    Fp : ℕ → Poly ⊤ ⊤
    Fp n = record { 
             γ = λ { tt → ⊤ } ; 
             ρ = λ { (tt , tt) → Fin n } ; 
             τ = λ _ → tt 
           }

    F : ℕ → PolyMonad ⊤ 
    F n = let open FreeM ⊤ (Fp n) in FrM

