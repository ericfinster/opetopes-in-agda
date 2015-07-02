--
--  IdentityMonad.agda - The Identity Monad
--
--  Eric Finster
--

open import Prelude
open import Polynomial
open import PolynomialMonad

module IdentityMonad where

  module IdentityM (I : Set) where

    open Poly

    id-η : IdP I ⇛ IdP I
    id-η = record { 
      γ-map = λ { i tt → tt } ; 
      ρ-eqv = λ { i tt → id-equiv (ρ (IdP I) (i , tt)) } ; 
      τ-coh = λ { i tt tt → idp } }

    id-μ : IdP I ⊚ IdP I ⇛ IdP I
    id-μ = record { 
      γ-map = λ { i x → tt } ; 
      ρ-eqv = λ { i x → record { 
            f = λ { (tt , tt) → tt } ; 
            g = λ { tt → (tt , tt) } ; 
            g-f = λ { (tt , tt) → idp } ; 
            f-g = λ { tt → idp } } } ; 
      τ-coh = λ { i x p → idp } }

    -- idM : PolyMonad I
    -- idM = record { 
    --   P = Id I ; 
    --   η = id-η ; 
    --   μ = id-μ }


