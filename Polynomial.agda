--
--  Polynomial.agda - Indexed Polynomials
--
--  Eric Finster
--

open import Prelude

module Polynomial where

  infixr 2 _⇛_
  infixl 4 _⊚_ 

  record Poly (I : Set) (J : Set) : Set₁ where

    field

      γ : I → Set
      ρ : Σ I γ → Set
      τ : Σ (Σ I γ) ρ → J

  ⟦_⟧ : {I J : Set} → Poly I J → (J → Set) → (I → Set)
  ⟦ P ⟧ X i = Σ[ c ∈ γ i ] ((p : ρ (i , c)) → X (τ ((i , c) , p)))
    where open Poly P

  _⊚_ : {I J K : Set} → Poly J K → Poly I J → Poly I K
  P ⊚ Q = let open Poly in 
    record { 
      γ = ⟦ Q ⟧ (γ P) ; 
      ρ = λ { (i , c , φ) → Σ[ p ∈ ρ Q (i , c) ] ρ P (τ Q ((i , c) , p) , φ p) } ; 
      τ = λ { ((i , c , φ) , p₀ , p₁) → τ P ((τ Q ((i , c) , p₀) , φ p₀) , p₁) } 
    }

  record _⇛_ {I J : Set} (P Q : Poly I J) : Set where

    open Poly
    open _≃_

    field

      γ-map : (i : I) → γ P i → γ Q i

      ρ-eqv : (i : I) → (c : γ P i) → 
              ρ P (i , c) ≃ ρ Q (i , γ-map i c)

      τ-coh : (i : I) → (c : γ P i) → (p : ρ P (i , c)) → 
              τ P ((i , c) , p) == τ Q ((i , γ-map i c) , (f (ρ-eqv i c) p))

    ρ-map : {i : I} → (c : γ P i) → ρ P (i , c) → ρ Q (i , γ-map i c)
    ρ-map c p = f (ρ-eqv _ c) p

    ρ-inv-map : {i : I} → (c : γ P i) → ρ Q (i , γ-map i c) → ρ P (i , c)
    ρ-inv-map c q = g (ρ-eqv _ c) q
  
    ρ-inv-left : {i : I} → {c : γ P i} → (p : ρ P (i , c)) → 
                 p == ρ-inv-map c (ρ-map c p)
    ρ-inv-left p = g-f (ρ-eqv _ _) p

    ρ-inv-right : {i : I} → {c : γ P i} → (q : ρ Q (i , γ-map i c)) → 
                  ρ-map c (ρ-inv-map c q) == q
    ρ-inv-right q = f-g (ρ-eqv _ _) q

  IdP : (I : Set) → Poly I I
  IdP I = record { 
           γ = λ i → ⊤ ; 
           ρ = λ { (i , tt) → ⊤ } ; 
           τ = λ { ((i , tt) , tt) → i } 
         }

  data W {I : Set} (P : Poly I I) : I → Set where
    leaf : (i : I) → W P i
    node : (i : I) → ⟦ P ⟧ (W P) i → W P i

  module _ {I : Set} {P : Poly I I} where

    open Poly P

    corolla : (i : I) → (c : γ i) → W P i
    corolla i c = node i (c , λ p → leaf _)

    typeOf : {i : I} → {c : γ i} → ρ (i , c) → I
    typeOf p = τ (_ , p)

    leafOf : {i : I} → W P i → Set
    leafOf (leaf i) = ⊤
    leafOf (node i (c , φ)) = Σ[ p ∈ ρ (i , c) ] leafOf (φ p)
      
    leafType : {i : I} → {w : W P i} → leafOf w → I
    leafType {w = leaf i} tt = i
    leafType {w = node ._ _} (_ , l) = leafType l

    nodeOf : {i : I} → W P i → Set
    nodeOf (leaf i) = ⊥
    nodeOf (node i (c , φ)) = ⊤ ⊎ (Σ[ p ∈ ρ (i , c) ] nodeOf (φ p))

    nodeType : {i : I} → {w : W P i} → nodeOf w → Σ I γ
    nodeType {w = leaf ._} ()
    nodeType {w = node i (c , _)} (inj₁ tt) = (i , c)
    nodeType {w = node ._ _} (inj₂ (_ , n)) = nodeType n


