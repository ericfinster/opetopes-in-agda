--
--  SliceMonad.agda - The slie monad of a polynomial monad
--
--  Eric Finster
--

open import Prelude
open import PolynomialMonad
open import FreeMonad

module SliceMonad where

  -- module SliceMonadDefn {I : Set} (M : PolyMonad I) where

  --   open PolyMonad M renaming (η to ηM ; μ to μM)
  --   open Poly P
  --   open _⇛_
  --   open _≃_

  --   collapse : {i : I} → W P i → γ i
  --   collapse (leaf i) = γ-map ηM i tt 
  --   collapse (node i (c , φ)) = γ-map μM i (c , (λ p → collapse (φ p)))

  --   B : Set
  --   B = Σ I γ

  --   SmP : Poly B B
  --   SmP = record { 
  --     γ = λ { (i , c) → fiber collapse c } ; 
  --     ρ = λ { ((i , c) , w , ev) → nodeOf w } ; 
  --     τ = λ { (((i , c) , w , ev) , n) → nodeType n } }

  --   corolla : (i : I) → (c : γ i) → W P i
  --   corolla i c = node i (c , (λ p → leaf (τ ((i , c) , p))))

  --   corolla-coh : (i : I) → (c : γ i) → collapse (corolla i c) == c
  --   corolla-coh i c = {!collapse (corolla i c)!}

  --   sm-η : Id B ⇛ SmP
  --   sm-η = record { 
  --     γ-map = λ { (i , c) → λ { tt → (corolla i c , corolla-coh i c) } } ; 
  --     ρ-eqv = {!!} ; 
  --     τ-coh = {!!} }

  --   sm-μ : SmP ⊚ SmP ⇛ SmP
  --   sm-μ = {!!}
    
  --   Sm : PolyMonad B
  --   Sm = record { P = SmP ; η = sm-η ; μ = sm-μ }

  -- module Opetopes where
  
  --   open Poly
  --   open PolyMonad

  --   mutual

  --     O : ℕ → Set
  --     O zero = ⊤
  --     O (suc n) = B
  --       where open SliceMonadDefn (S n)

  --     S : (n : ℕ) → PolyMonad (O n)
  --     S zero = IdM ⊤
  --     S (suc n) = Sm
  --       where open SliceMonadDefn (S n)

  --   object : O 0
  --   object = tt

  --   arrow : O 1
  --   arrow = tt , tt

  --   drop : O 2
  --   drop = arrow , (leaf tt , idp)

  --   2-glob : O 2
  --   2-glob = arrow , (node tt (tt , (λ { tt → leaf tt }))) , idp

  --   -- record OSet (I : Set) (P : PolyMonad I) : Set₁ where
  --   --   coinductive
  --   --   field

  --   --     J : Set
  --   --     f : J → I

  --   --   open Pullback J I f P
  --   --   open SliceMonadDefn PbM
       
  --   --   field
  
  --   --     hom : ∞ (OSet B Sm)
      
