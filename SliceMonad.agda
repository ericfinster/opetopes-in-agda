--
--  SliceMonad.agda - The slice monad of a polynomial monad
--
--  Eric Finster
--

open import Prelude
open import Polynomial
open import PolynomialMonad
open import FreeMonad

module SliceMonad where

  module SliceM {I : Set} (M : PolyMonad I) where

    open PolyMonad M renaming (η to ηM ; μ to μM)
    open CollapseLemmas M
    open FreeMonad
    open Poly
    open _⇛_
    open _≃_

    B : Set
    B = Σ I (γ P)

    SmP : Poly B B
    SmP = record { 
      γ = λ { (i , c) → fiber collapse c } ; 
      ρ = λ { ((i , c) , w , ev) → nodeOf w } ; 
      τ = λ { (((i , c) , w , ev) , n) → nodeType n } }

    corolla-has-one-node : {i : I} → (c : γ P i) → ⊤ ≃ nodeOf (corolla {P = P} i c) 
    corolla-has-one-node c = record { 
      f = λ { tt → inj₁ tt } ; 
      g = λ { _ → tt } ; 
      g-f = λ { tt → idp } ; 
      f-g = λ { (inj₁ tt) → idp ; 
                (inj₂ (_ , ())) } }

    sm-η : IdP B ⇛ SmP
    sm-η = record { 
      γ-map = λ { (i , c) tt → (corolla i c , unit-leaf-law c) } ;
      ρ-eqv = λ { (i , c) tt → corolla-has-one-node c } ; 
      τ-coh = λ { (i , c) tt tt → idp } }

    {-# TERMINATING #-}
    sm-graft : (b : B) → γ (SmP ⊚ SmP) b → γ SmP b
    sm-graft (i , ._) ((leaf .i , idp) , _) = γ-map sm-η (i , _) tt
    sm-graft (i , ._) ((node .i (c , Φ) , idp) , Ψ) = 
      fm-graft i (localTree , λ l → proj₁ (IH l)) , {!!}  

      where open FreeM I P
            open AssocLemmas FmP fm-μ

            localCons : γ SmP (i , c)
            localCons = (Ψ (inj₁ tt))

            localTree : W P i
            localTree = proj₁ localCons

            localEv : collapse localTree == c
            localEv = proj₂ localCons
  
            resultLeaf : leafOf localTree → ρ P (i , c)
            resultLeaf l = transport (ρ P) (ap (λ c₀ → (i , c₀)) localEv) (collapse-leaf localTree l) 

            leafCoh : (l : leafOf localTree) → leafType l == τ P ((i , c) , resultLeaf l)
            leafCoh l = {!!}

            nextTree : (l : leafOf localTree) → W P (leafType l)
            nextTree l = transport! (W P) (leafCoh l) (Φ (resultLeaf l))

            nextCons : (l : leafOf localTree) → γ P (leafType l)
            nextCons l = transport! (γ P) (leafCoh l) (collapse (Φ (resultLeaf l)))

            nextCoh : (l : leafOf localTree) → collapse (nextTree l) == nextCons l
            nextCoh l = transport!-fun-coh (W P) (γ P) (leafCoh l) (Φ (resultLeaf l)) collapse

            nodeCoe : (l : leafOf localTree) → (n : nodeOf (nextTree l)) → nodeOf (node i (c , Φ))
            nodeCoe l n = inj₂ (resultLeaf l , transport!-comp (W P) nodeOf (leafCoh l) (Φ (resultLeaf l)) n) 

            nodeCoh : (l : leafOf localTree) → (n : nodeOf (nextTree l)) → nodeType {w = nextTree l} n == nodeType (nodeCoe l n)
            nodeCoh l n = {!!}

            Ψ' : (n : nodeOf {i = i} (node i (c , Φ))) → γ SmP (nodeType {w = node i (c , Φ)} n)
            Ψ' = Ψ

            nextDec : (l : leafOf localTree) → (n : nodeOf (nextTree l)) → γ SmP (nodeType {w = nextTree l} n)
            nextDec l n = {!!} -- transport (γ SmP) (nodeCoh l n) (Ψ' (nodeCoe l n))

            IH : (l : leafOf localTree) → γ SmP (leafType l , nextCons l)
            IH l = sm-graft (leafType l , nextCons l) ((nextTree l , nextCoh l) , nextDec l)

    sm-place-eqv : (b : B) → (d : γ (SmP ⊚ SmP) b) → ρ (SmP ⊚ SmP) (b , d) ≃ ρ SmP (b , sm-graft b d)
    sm-place-eqv b d = {!!}

    sm-type-coh : (b : B) → (d : γ (SmP ⊚ SmP) b) → (n : ρ (SmP ⊚ SmP) (b , d)) → 
                  τ (SmP ⊚ SmP) ((b , d), n) == τ SmP ((b , sm-graft b d) , f (sm-place-eqv b d) n)
    sm-type-coh b d n = {!!}

    sm-μ : SmP ⊚ SmP ⇛ SmP
    sm-μ = record { 
      γ-map = sm-graft ; 
      ρ-eqv = sm-place-eqv ; 
      τ-coh = sm-type-coh }

    open UnitLemmas SmP sm-η
    open AssocLemmas SmP sm-μ
    
    postulate

      sm-unit-leaf-law : {b : B} (d : γ SmP b) → mult (unit-leaf-decor d) == d
      sm-unit-root-law : {b : B} (d : γ SmP b) → mult (unit-root-decor d) == d

      sm-assoc-law : {b : B} (d : γ (SmP ⊚ SmP ⊚ SmP) b) → 
                     mult (mult-left d) == mult (mult-right (decor-assoc-right b d))

    Sm : PolyMonad B
    Sm = record
           { P = SmP
           ; η = sm-η
           ; μ = sm-μ
           ; unit-leaf-law = sm-unit-leaf-law
           ; unit-root-law = sm-unit-root-law
           ; assoc-law = sm-assoc-law
           }

