--
--  Opetopes.agda - Opetopes in agda
--
--  Eric Finster
--

open import Prelude
open import Polynomial
open import PolynomialMonad

module Opetopes where
    
  open Poly
  open PolyMonad

  -- mutual

  --   O : ℕ → Set
  --   O zero = ⊤
  --   O (suc n) = B
  --   where open SliceMonadDefn (S n)

  --   S : (n : ℕ) → PolyMonad (O n)
  --   S zero = IdM ⊤
  --   S (suc n) = Sm
  --   where open SliceMonadDefn (S n)
  
  -- object : O 0
  -- object = tt

  -- arrow : O 1
  -- arrow = tt , tt

  -- drop : O 2
  -- drop = arrow , (leaf tt , idp)

  -- 2-glob : O 2
  -- 2-glob = arrow , (node tt (tt , (λ { tt → leaf tt }))) , idp

-- record OSet (I : Set) (P : PolyMonad I) : Set₁ where
--   coinductive
--   field

--     J : Set
--     f : J → I

--   open Pullback J I f P
--   open SliceMonadDefn PbM

--   field

--     hom : ∞ (OSet B Sm)

