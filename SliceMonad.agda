--
--  SliceMonad.agda - The slice monad of a polynomial monad
--
--  Eric Finster
--

open import Prelude
open import Polynomial
open import PolynomialMonad
--open import FreeMonad

module SliceMonad where

  module SliceM {I : Set} (M : PolyMonad I) where

    open PolyMonad M renaming (η to ηM ; μ to μM)
    open Poly P
    open _⇛_
    open _≃_

    collapse : {i : I} → W P i → γ i
    collapse (leaf i) = γ-map ηM i tt 
    collapse (node i (c , φ)) = γ-map μM i (c , (λ p → collapse (φ p)))

    B : Set
    B = Σ I γ

    SmP : Poly B B
    SmP = record { 
      γ = λ { (i , c) → fiber collapse c } ; 
      ρ = λ { ((i , c) , w , ev) → nodeOf w } ; 
      τ = λ { (((i , c) , w , ev) , n) → nodeType n } }

    sm-η : IdP B ⇛ SmP
    sm-η = record { 
      γ-map = {!!} ;
      ρ-eqv = {!!} ; 
      τ-coh = {!!} }

  --   sm-μ : SmP ⊚ SmP ⇛ SmP
  --   sm-μ = {!!}
    
  --   Sm : PolyMonad B
  --   Sm = record { P = SmP ; η = sm-η ; μ = sm-μ }

