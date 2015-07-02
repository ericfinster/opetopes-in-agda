--
--  Prelude.agda - Basic definitions
--
--  Eric Finster
--

module Prelude where

  infixr 4 _,_
  infixr 2 _×_
  infixr 1 _⊎_

  data ℕ : Set where
    zero : ℕ
    suc  : (n : ℕ) → ℕ

  {-# BUILTIN NATURAL ℕ #-}

  record ⊤ : Set where
    constructor tt

  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁

  open Σ public

  Σ-syntax : ∀ (A : Set) → (A → Set) → Set 
  Σ-syntax = Σ

  syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

  _×_ : ∀ (A : Set) (B : Set) → Set
  A × B = Σ[ x ∈ A ] B

  data ⊥ : Set where

  {-# IMPORT Data.FFI #-}
  {-# COMPILED_DATA ⊥ Data.FFI.AgdaEmpty #-}

  data _⊎_ (A : Set) (B : Set) : Set where
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

  infixr 8 _∙_

  _∙_ : ∀ {i} → {A : Set i} → {x y z : A}
    → (x == y → y == z → x == z)
  idp ∙ q = q
  
  ! : ∀ {i} → {A : Set i} → {x y : A} → (x == y → y == x)
  ! idp = idp

  has-all-paths : (A : Set) → Set
  has-all-paths A = (x y : A) → x == y

  unit-has-all-paths : has-all-paths ⊤
  unit-has-all-paths tt tt = idp

  record _≃_ (A B : Set) : Set where

    field

      f : A → B
      g : B → A

      g-f : (a : A) → a == g (f a)
      f-g : (b : B) → f (g b) == b

  id-equiv : (A : Set) → A ≃ A
  id-equiv A = record { 
                 f = λ a → a ; 
                 g = λ a → a ; 
                 g-f = λ a → idp ; 
                 f-g = λ a → idp 
               }

  Σ-eqv-base : (A : Set) → (Σ[ u ∈ ⊤ ] A) ≃ A
  Σ-eqv-base A = record { 
    f = λ { (tt , a) → a } ; 
    g = λ a → (tt , a) ; 
    g-f = λ _ → idp ; 
    f-g = λ _ → idp }

  Σ-eqv-lift : (A : Set) (P : A → Set) (Q : Σ A P → Set) → 
               (Σ (Σ A P) Q) ≃ Σ A (λ a → Σ (P a) (λ p → Q (a , p)))
  Σ-eqv-lift A P Q = record { 
    f = λ { ((a , p) , q) → a , (p , q) } ; 
    g = λ { (a , p , q) → (a , p) , q } ; 
    g-f = λ _ → idp ; 
    f-g = λ _ → idp }

  Σ-eqv-inv : (A : Set) (P Q : A → Set) → ((a : A) → P a ≃ Q a) → Σ A P ≃ Σ A Q
  Σ-eqv-inv A P Q φ = record { 
    f = λ { (a , p) → a , f (φ a) p } ; 
    g = λ { (a , q) → a , g (φ a) q } ; 
    g-f = λ { (a , p) → ap (λ x → a , x) (g-f (φ a) p) } ; 
    f-g = λ { (a , q) → ap (λ x → a , x) (f-g (φ a) q) } }

    where open _≃_

  _⊙_ : {A B C : Set} → B ≃ C → A ≃ B → A ≃ C
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
    ∞  : ∀ {a} (A : Set a) → Set a
    ♯_ : ∀ {a} {A : Set a} → A → ∞ A
    ♭  : ∀ {a} {A : Set a} → ∞ A → A

  {-# BUILTIN INFINITY ∞  #-}
  {-# BUILTIN SHARP    ♯_ #-}
  {-# BUILTIN FLAT     ♭  #-}
