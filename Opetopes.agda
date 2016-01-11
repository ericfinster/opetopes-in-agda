{-# OPTIONS --copatterns #-}
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

  -- Streams

  record Stream {i} (A : Set i) : Set i where
    coinductive
    field
      head : A
      tail : Stream A

  open Stream

  get : ∀ {i} {A : Set i} → Stream A → ℕ → A
  get s zero = head s
  get s (suc n) = get (tail s) n

  smap : ∀ {i} {A B : Set i} (f : A → B) → Stream A → Stream B
  head (smap f sa) = f (head sa)
  tail (smap f sa) = smap f (tail sa)

  record StreamMap (A B : Stream Set) : Set where
    coinductive
    field
      hmap : head A → head B
      tmap : StreamMap (tail A) (tail B)

  open StreamMap

  -- Opetopic Sets

  record OSet {I : Set} (M : PolyMonad I) : Set₁ where
    coinductive
    field

      X : I → Set
      hom : OSet (SlM (PbM X M))

  open OSet

  terminal : {I : Set} (M : PolyMonad I) → OSet M
  X (terminal M) = λ i → ⊤
  hom (terminal M) = terminal (SlM (PbM (λ i → ⊤) M))

  empty : {I : Set} (M : PolyMonad I) → OSet M
  X (empty M) = λ i → ⊥
  hom (empty M) = empty (SlM (PbM (λ i → ⊥) M))

  sliceStream : ∀ {I : Set} (M : PolyMonad I) → Stream (Σ[ J ∈ Set ] PolyMonad J)
  head (sliceStream M) = _ , M
  tail (sliceStream M) = sliceStream (SlM M)

  opStream : ∀ {I : Set} (M : PolyMonad I) → Stream Set
  opStream M = smap proj₁ (sliceStream M)

  frameStream : ∀ {I : Set} {M : PolyMonad I} (A : OSet M) → Stream Set
  head (frameStream {I} A) = I
  tail (frameStream A) = frameStream (hom A)

  cellStream : ∀ {I : Set} {M : PolyMonad I} (A : OSet M) → Stream Set
  head (cellStream A) = Σ _ (X A)
  tail (cellStream A) = cellStream (hom A)

  nicheStream : ∀ {I : Set} {M : PolyMonad I} (A : OSet M) → Stream Set
  head (nicheStream {I} {M} A) = Σ[ i ∈ I ] (⟦ P M ⟧ (X A) i)  -- I think this is right ....
  tail (nicheStream A) = nicheStream (hom A)

  bdryStream : ∀ {I : Set} {M : PolyMonad I} (A : OSet M) → StreamMap (cellStream A) (frameStream A)
  hmap (bdryStream A) = proj₁
  tmap (bdryStream A) = bdryStream (hom A)

  -- So, punctured niches are a bit of a problem.  For this we are going to
  -- need to redo polynomials with the assumption that the places are decidable.
  -- In this case we will be able to consider punctured niches using derivatives!

  -- Opetopes and examples

  O : ℕ → Set
  O n = get (opStream (IdM ⊤)) n
  
  object : O 0
  object = tt

  arrow : O 1
  arrow = tt , tt

  2-drop : O 2
  2-drop = (tt , tt) , (leaf tt) , idp

  2-glob : O 2
  2-glob = (tt , tt) , (node tt (tt , (λ { tt → leaf tt })) , idp)

  glob : (n : ℕ) → O n → O (suc n)
  glob zero o = tt , tt
  glob (suc n) o = {!!}
