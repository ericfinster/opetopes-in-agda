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

    FmP : Poly I I
    FmP = record { 
            γ = W P ; 
            ρ = λ { (i , w) → leafOf w } ; 
            τ = λ { ((i , w) , l) → leafType l } 
          }

    fm-η : IdP I ⇛ FmP
    fm-η = record { 
             γ-map = λ i c → leaf i ; 
             ρ-eqv = λ i c → id-equiv ⊤ ;
             τ-coh = λ i c p → idp
           }

    {-# TERMINATING #-}
    fm-graft : (i : I) → γ (FmP ⊚ FmP) i → γ FmP i
    fm-graft i (leaf .i , ψ) = ψ tt
    fm-graft i (node .i (c , φ) , ψ) = 
      node i (c , (λ p₀ → fm-graft (τ P ((i , c) , p₀)) (φ p₀ , (λ p₁ → ψ (p₀ , p₁)))))

    {-# TERMINATING #-}
    fm-grafting-eqv : (i : I) (c : γ (FmP ⊚ FmP) i) → ρ (FmP ⊚ FmP) (i , c) ≃ ρ FmP (i , fm-graft i c)
    fm-grafting-eqv i (leaf .i , ψ) = Σ-eqv-base (ρ FmP (i , (ψ tt)))
    fm-grafting-eqv i (node .i (c , φ) , ψ) = 
      Σ-eqv-inv (ρ P (i , c)) _ _ (λ p → fm-grafting-eqv (τ P ((i , c) , p)) (φ p , (λ p₀ → ψ (p , p₀)))) ⊙ (Σ-eqv-lift _ _ _)

    {-# TERMINATING #-}
    fm-type-coh : (i : I) (c : γ (FmP ⊚ FmP) i) (p : ρ (FmP ⊚ FmP) (i , c)) →
                  τ (FmP ⊚ FmP) ((i , c) , p) ==
                  τ FmP ((i , fm-graft i c) , f (fm-grafting-eqv i c) p)
    fm-type-coh i (leaf .i , ψ) (p₀ , p₁) = idp
    fm-type-coh i (node .i (c , φ) , ψ) ((p , l₀) , l₁) = 
      leafType l₁ =⟨ fm-type-coh (τ P ((i , c) , p)) (φ p , (λ p₀ → ψ (p , p₀))) (l₀ , l₁)  ⟩ 
      leafType (f (fm-grafting-eqv (τ P ((i , c) , p)) (φ p , (λ p₀ → ψ (p , p₀)))) (l₀ , l₁)) ∎
  
    fm-μ : FmP ⊚ FmP ⇛ FmP
    fm-μ = record { 
             γ-map = fm-graft ; 
             ρ-eqv = fm-grafting-eqv ; 
             τ-coh = fm-type-coh 
           }

    open UnitLemmas FmP fm-η
    open AssocLemmas FmP fm-μ

    fm-unit-leaf-law : {i : I} (c : γ FmP i) → mult (unit-leaf-decor c) == c
    fm-unit-leaf-law (leaf i) = idp
    fm-unit-leaf-law (node i (c , φ)) = ap (λ φ₀ → node i (c , φ₀)) (funext IH)

      where IH : (p : ρ P (_ , c)) → mult (unit-leaf-decor (φ p)) == φ p
            IH p = fm-unit-leaf-law (φ p)

    fm-unit-root-law : {i : I} (c : γ FmP i) → mult (unit-root-decor c) == c
    fm-unit-root-law (leaf i) = idp
    fm-unit-root-law (node i (c , φ)) = idp

    module _ {i : I} {c : γ P i}
      (φ : (p : ρ P (i , c)) → W P (τ P (_ , p)))
      (ψ : (p : leafOf (node i (c , φ))) → γ (FmP ⊚ FmP) (τ FmP (_ , p)))
      (p₀ : ρ P (_ , c)) (l : leafOf (mult (φ p₀ , (λ p₁ → proj₁ (ψ (p₀ , p₁)))))) where

      d : γ (FmP ⊚ FmP) _
      d = (φ p₀ , (λ p₁ → proj₁ (ψ (p₀ , p₁))))
        
      main-lemma : transport (W P) (lift-place-coh {d = d} l) (proj₂ (ψ (p₀ , proj₁ (lift-place l))) (proj₂ (lift-place {d = d} l))) == 
                   induced-decor (proj₂ (decor-assoc-right i (_ , ψ))) (p₀ , l) 
                   -- transport (W P) (lift-place-coh (p₀ , l)) ((λ { (p₁ , p₂) → proj₂ (ψ p₁) p₂}) (lift-place (p₀ , l)))
      main-lemma = {!!}

    {-# TERMINATING #-}
    fm-assoc-law : {i : I} (c : γ (FmP ⊚ FmP ⊚ FmP) i) →
                   mult (mult-left c) == mult (mult-right (decor-assoc-right i c))
    fm-assoc-law (leaf i , ψ) = idp
    fm-assoc-law (node i (c , φ) , ψ) =
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
            IH p = fm-assoc-law (φ p , (λ p₁ → ψ (p , p₁)))

            lemma : (p₀ : ρ P (i , c)) → induced-decor (λ { (p₁ , p₂) → proj₂ (ψ (p₀ , p₁)) p₂ }) == 
                                         (λ q → (induced-decor (λ { (p₀ , p₁) → proj₂ (ψ p₀) p₁ })) (p₀ , q))
            lemma p₀ = 
              induced-decor (λ { (p₁ , p₂) → proj₂ (ψ (p₀ , p₁)) p₂ }) =⟨ funext (main-lemma φ ψ p₀) ⟩ 
              (λ q → (induced-decor (λ { (p₀ , p₁) → proj₂ (ψ p₀) p₁ })) (p₀ , q)) ∎

            lemma₀ : (p₀ : ρ P (i , c)) → mult (mult (φ p₀ , (λ p₁ → proj₁ (ψ (p₀ , p₁)))) , induced-decor (λ { (p₁ , p₂) → proj₂ (ψ (p₀ , p₁)) p₂ })) ==
                                          mult (mult (φ p₀ , (λ p₁ → proj₁ (ψ (p₀ , p₁)))) , ((λ q → (induced-decor (λ { (p₀ , p₁) → proj₂ (ψ p₀) p₁ })) (p₀ , q))))
            lemma₀ p₀ = ap (λ X → mult (mult (φ p₀ , (λ p₁ → proj₁ (ψ (p₀ , p₁)))) , X)) (lemma p₀) 

    Fm : PolyMonad I
    Fm = record
           { P = FmP
           ; η = fm-η
           ; μ = fm-μ
           ; unit-leaf-law = fm-unit-leaf-law
           ; unit-root-law = fm-unit-root-law
           ; assoc-law = fm-assoc-law
           }

