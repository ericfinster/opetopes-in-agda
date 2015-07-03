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
    open FreeMonad
    open Poly
    open _⇛_
    open _≃_

    collapse : {i : I} → W P i → γ P i
    collapse (leaf i) = γ-map ηM i tt 
    collapse (node i (c , φ)) = γ-map μM i (c , (λ p → collapse (φ p)))

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

    sm-graft : (b : B) → γ (SmP ⊚ SmP) b → γ SmP b
    sm-graft (i , ._) ((leaf .i , idp) , _) = γ-map sm-η (i , _) tt
    sm-graft (i , ._) ((node .i (c , Φ) , idp) , Ψ) = 
      fm-graft i (localTree , newDecor) , {!proj₂ (Ψ (inj₁ tt))!}  

      where open FreeM I P
            open AssocLemmas FmP fm-μ

            localTree : W P i
            localTree = proj₁ (Ψ (inj₁ tt))

            localEv : collapse localTree == c
            localEv = proj₂ (Ψ (inj₁ tt))
  
            resultLeaf : leafOf localTree → ρ P (i , c)
            resultLeaf l = {!!}

            leafCoh : (l : leafOf localTree) → leafType l == τ P ((i , c) , resultLeaf l)
            leafCoh l = {!!}

            newDecor : (l : leafOf localTree) → γ FmP (τ FmP ((i , localTree), l))
            newDecor l = proj₁ (sm-graft (leafType l , transport! (γ P) (leafCoh l) (collapse (Φ (resultLeaf l)))) ({!!} , {!!}))

      -- Well, not quite.  This is only a two level decoration.  So the base type 
      -- seems to work out very nicely.  But what we want to return is the multiplication
      -- of this with the recursive call ...

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

      fm-unit-leaf-law : {b : B} (d : γ SmP b) → mult (unit-leaf-decor d) == d
      fm-unit-root-law : {b : B} (d : γ SmP b) → mult (unit-root-decor d) == d

      fm-assoc-law : {b : B} (d : γ (SmP ⊚ SmP ⊚ SmP) b) → 
                     mult (mult-left d) == mult (mult-right (decor-assoc-right b d))

    Sm : PolyMonad B
    Sm = record
           { P = SmP
           ; η = sm-η
           ; μ = sm-μ
           ; unit-leaf-law = fm-unit-leaf-law
           ; unit-root-law = fm-unit-root-law
           ; assoc-law = fm-assoc-law
           }

