--
--  Prelude.agda - Basic definitions
--
--  Eric Finster
--

module Prelude where

  open import Agda.Primitive public 

  infixr 4 _,_
  -- infixr 2 _×_
  -- infixr 1 _⊎_

  data ℕ : Set where
    zero : ℕ
    suc  : (n : ℕ) → ℕ

  {-# BUILTIN NATURAL ℕ #-}

  record ⊤ : Set where
    constructor tt

  record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁

  open Σ public

  Σ-syntax : ∀ {i j} (A : Set i) → (A → Set j) → Set (i ⊔ j)
  Σ-syntax = Σ

  syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

  _×_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
  A × B = Σ[ x ∈ A ] B

  data ⊥ : Set where

  {-# IMPORT Data.FFI #-}
  {-# COMPILED_DATA ⊥ Data.FFI.AgdaEmpty #-}

  data _⊎_ {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
    inj₁ : (x : A) → A ⊎ B
    inj₂ : (y : B) → A ⊎ B

  {-# IMPORT Data.FFI #-}
  {-# COMPILED_DATA _⊎_ Data.FFI.AgdaEither Left Right #-}

  data _==_ {i} {A : Set i} (a : A) : A → Set i where
    idp : a == a

  {-# BUILTIN EQUALITY _==_ #-}
  {-# BUILTIN REFL  idp #-}

  infix  2 _∎
  infixr 2 _=⟨_⟩_

  _=⟨_⟩_ : ∀ {i} {A : Set i} (x : A) {y z : A} → x == y → y == z → x == z
  _ =⟨ idp ⟩ idp = idp

  _∎ : ∀ {i} {A : Set i} (x : A) → x == x
  _ ∎ = idp

  syntax ap f p = p |in-ctx f

  fiber : {A B : Set} → (f : A → B) → B → Set
  fiber f b = Σ[ a ∈ _ ] f a == b

  ap : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A}
    → (x == y → f x == f y)
  ap f idp = idp

  ap-2 : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A} {p q : x == y} →
         (p == q) → ap f p == ap f q
  ap-2 f idp = idp

  coe : ∀ {i} {A B : Set i} (p : A == B) → A → B
  coe idp x = x

  coe! : ∀ {i} {A B : Set i} (p : A == B) → B → A
  coe! idp x = x

  transport : ∀ {i j} {A : Set i} (B : A → Set j) {x y : A} (p : x == y)
    → (B x → B y)
  transport B p = coe (ap B p)

  transport! : ∀ {i j} {A : Set i} (B : A → Set j) {x y : A} (p : x == y)
    → (B y → B x)
  transport! B p = coe! (ap B p)

  transport-comp : ∀ {i j} {A : Set i} (B : A → Set j) (C : {a : A} → B a → Set j)
                   {x y : A} (p : x == y) (e : B x) (α : C (transport B p e)) → C e
  transport-comp B C idp e α = α

  transport!-comp : ∀ {i j} {A : Set i} (B : A → Set j) (C : {a : A} → B a → Set j)
                   {x y : A} (p : x == y) (f : B y) (β : C (transport! B p f)) → C f
  transport!-comp B C idp f β = β

  transport-fun-coh : ∀ {i j} {A : Set i} (B C : A → Set j) {x y : A} (p : x == y) (e : B x)
                      (φ : {a : A} → B a → C a) → φ (transport B p e) == transport C p (φ e)
  transport-fun-coh B C idp e φ = idp

  transport!-fun-coh : ∀ {i j} {A : Set i} (B C : A → Set j) {x y : A} (p : x == y) (f : B y)
                      (φ : {a : A} → B a → C a) → φ (transport! B p f) == transport! C p (φ f)
  transport!-fun-coh B C idp e f = idp

  transport-coh : ∀ {i j} {A : Set i} (B : A → Set j) {x y : A} {p q : x == y} → 
                  (α : p == q) → (e : B x) → transport B p e == transport B q e
  transport-coh B idp e = idp

  transport!-coh : ∀ {i j} {A : Set i} (B : A → Set j) {x y : A} {p q : x == y} → 
                   (α : p == q) → (f : B y) → transport! B p f == transport! B q f
  transport!-coh B idp f = idp

  infixr 8 _∙_

  _∙_ : ∀ {i} → {A : Set i} → {x y z : A}
    → (x == y → y == z → x == z)
  idp ∙ q = q
  
  ! : ∀ {i} → {A : Set i} → {x y : A} → (x == y → y == x)
  ! idp = idp

  has-all-paths : Set → Set
  has-all-paths A = (x y : A) → x == y

  unit-has-all-paths : has-all-paths ⊤
  unit-has-all-paths tt tt = idp

  K : {A : Set} {x y : A} (p q : x == y) → p == q
  K idp idp = idp

  record _≃_ {i} (A B : Set i) : Set i where

    field

      f : A → B
      g : B → A

      g-f : (a : A) → a == g (f a)
      f-g : (b : B) → f (g b) == b

  id-equiv : ∀ {i} (A : Set i) → A ≃ A
  id-equiv A = record { 
                 f = λ a → a ; 
                 g = λ a → a ; 
                 g-f = λ a → idp ; 
                 f-g = λ a → idp 
               }

  Σ-transport : ∀ {i j} {A : Set i} → {P : A → Set j} → {a b : A} → {x : P a} → 
                (p : a == b) → (a , x) == (b , transport P p x)
  Σ-transport idp = idp

  Σ-transport! : ∀ {i j} {A : Set i} → {P : A → Set j} → {a b : A} → {y : P b} → 
                 (p : a == b) → (b , y) == (a , transport! P p y)
  Σ-transport! idp = idp

  Σ-eqv-base : ∀ {i} (A : Set i) → (Σ[ u ∈ ⊤ ] A) ≃ A
  Σ-eqv-base A = record { 
    f = λ { (tt , a) → a } ; 
    g = λ a → (tt , a) ; 
    g-f = λ _ → idp ; 
    f-g = λ _ → idp }

  Σ-eqv-lift : ∀ {i j k} (A : Set i) (P : A → Set j) (Q : Σ A P → Set k) → 
               (Σ (Σ A P) Q) ≃ Σ A (λ a → Σ (P a) (λ p → Q (a , p)))
  Σ-eqv-lift A P Q = record { 
    f = λ { ((a , p) , q) → a , (p , q) } ; 
    g = λ { (a , p , q) → (a , p) , q } ; 
    g-f = λ _ → idp ; 
    f-g = λ _ → idp }

  Σ-eqv-inv : ∀ {i j} (A : Set i) (P Q : A → Set j) → ((a : A) → P a ≃ Q a) → Σ A P ≃ Σ A Q
  Σ-eqv-inv A P Q φ = record { 
    f = λ { (a , p) → a , f (φ a) p } ; 
    g = λ { (a , q) → a , g (φ a) q } ; 
    g-f = λ { (a , p) → ap (λ x → a , x) (g-f (φ a) p) } ; 
    f-g = λ { (a , q) → ap (λ x → a , x) (f-g (φ a) q) } }

    where open _≃_

  _⊙_ : ∀ {i} {A B C : Set i} → B ≃ C → A ≃ B → A ≃ C
  φ ⊙ ψ = record { 
    f = λ a → (f φ) ((f ψ) a) ; 
    g = λ c → (g ψ) ((g φ) c) ; 
    g-f = λ a → g-f ψ a ∙ ap (g ψ) (g-f φ (f ψ a)) ; 
    f-g = λ c → ap (f φ) (f-g ψ (g φ c)) ∙ f-g φ c } 

    where open _≃_

  equiv-unit-has-all-paths : (A : Set) → ⊤ ≃ A → has-all-paths A
  equiv-unit-has-all-paths A e x y = 
    x =⟨ ! (f-g x) ⟩
    f (g x) =⟨ ap f idp ⟩
    f (g y) =⟨ f-g y ⟩
    y ∎

    where open _≃_ e

  postulate
    ∞  : ∀ {i} (A : Set i) → Set i
    ♯ : ∀ {i} {A : Set i} → A → ∞ A
    ♭  : ∀ {i} {A : Set i} → ∞ A → A

  {-# BUILTIN INFINITY ∞  #-}
  {-# BUILTIN SHARP    ♯  #-}
  {-# BUILTIN FLAT     ♭  #-}

  postulate

    funext : ∀ {i j} {A : Set i} {P : A → Set j} → {f g : (a : A) → P a} → ((a : A) → f a == g a) → f == g
