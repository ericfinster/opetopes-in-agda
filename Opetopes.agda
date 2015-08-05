--
--  Opetopes.agda - Opetopes in agda
--
--  Eric Finster
--

open import Prelude
open import Polynomial
open import PolynomialMonad
open import IdentityMonad
open import PullbackMonad
open import SliceMonad

module Opetopes where
    
  open Poly
  open PolyMonad
  open Pullback
  open IdentityM
  open SliceM

  nth-slice : {I : Set} → (M : PolyMonad I) → ℕ → Σ[ J ∈ Set ] PolyMonad J
  nth-slice M zero = _ , M
  nth-slice M (suc n) = B S , SlM S
    
    where S : PolyMonad (proj₁ (nth-slice M n))
          S = proj₂ (nth-slice M n)

  O : ℕ → Set
  O n = proj₁ (nth-slice (IdM ⊤) n)

  record OSet {I : Set} (M : PolyMonad I) : Set₁ where
    coinductive
    field

      X : I → Set
      hom : ∞ (OSet (SlM (PbM _ X M)))

  trivial-slices : {I : Set} (M : PolyMonad I) → OSet M
  trivial-slices {I} M = 
    record { 
      X = λ i → ⊤ ; 
      hom = ♯ (trivial-slices (SlM (PbM _ _ M))) 
    }

  
