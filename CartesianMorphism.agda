{-# OPTIONS --without-K #-}

open import HoTT

open import Polynomial

module CartesianMorphism where

  record CartesianMorphism {ℓ} {I J K L : Type ℓ} (f : I → K) (g : J → L) (P : Poly I J) (Q : Poly K L) : Type ℓ where
    field

      γ-map : {j : J} → γ P j → γ Q (g j)
      ρ-eqv : {j : J} {c : γ P j} → ρ P c ≃ ρ Q (γ-map c)
      τ-coh : {j : J} {c : γ P j} (p : ρ P c) → f (τ P p) == τ Q (–> ρ-eqv p)

  open CartesianMorphism public

  ⟦_∣_⟧⟦_⇒_⟧ : ∀ {ℓ} {I J K L : Type ℓ} (f : I → K) (g : J → L) (P : Poly I J) (Q : Poly K L) → Type ℓ
  ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧ = CartesianMorphism f g P Q

  infixl 30 _⇝_

  _⇝_ : ∀ {ℓ} {I J : Type ℓ} (P Q : Poly I J) → Type ℓ
  P ⇝ Q = ⟦ (λ i → i) ∣ (λ j → j) ⟧⟦ P ⇒ Q ⟧

  poly-id : ∀ {ℓ} {I J : Type ℓ} (P : Poly I J) → P ⇝ P
  γ-map (poly-id P) = idf _
  ρ-eqv (poly-id P) = ide _
  τ-coh (poly-id P) p = idp

  module _ {ℓ} {I J K L : Type ℓ}
           {f : I → K} {g : J → L}
           {P : Poly I J} {Q : Poly K L}
           (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) {j : J} where

    ⟪_⟫ : γ P j → γ Q (g j)
    ⟪_⟫ = γ-map α

    ⟪_ⓐ_⟫≃ : (c : γ P j) → ρ P c ≃ ρ Q (⟪_⟫ c)
    ⟪_ⓐ_⟫≃ c = ρ-eqv α {c = c}

    ⟪_ⓐ_⟫↓ : (c : γ P j) → ρ P c → ρ Q (⟪_⟫ c)
    ⟪_ⓐ_⟫↓ c = –> (⟪_ⓐ_⟫≃ c)

    ⟪_ⓐ_⟫↑ : (c : γ P j) → ρ Q (⟪_⟫ c) → ρ P c
    ⟪_ⓐ_⟫↑ c = <– (⟪_ⓐ_⟫≃ c)

    ⟪_ⓐ_⟫⇵ : (c : γ P j) (p : ρ P c) → ⟪_ⓐ_⟫↑ c (⟪_ⓐ_⟫↓ c p) == p
    ⟪_ⓐ_⟫⇵ c = <–-inv-l (⟪_ⓐ_⟫≃ c)

    ⟪_ⓐ_⟫⇅ : (c : γ P j) (q : ρ Q (⟪_⟫ c)) → ⟪_ⓐ_⟫↓ c (⟪_ⓐ_⟫↑ c q) == q
    ⟪_ⓐ_⟫⇅ c = <–-inv-r (⟪_ⓐ_⟫≃ c)

    ⟪_ⓐ_⟫↓= : (c : γ P j) (p : ρ P c) → f (τ P p) == τ Q (⟪_ⓐ_⟫↓ c p)
    ⟪_ⓐ_⟫↓= c = τ-coh α {c = c}

    ⟪_ⓐ_⟫↑= : (c : γ P j) (q : ρ Q (⟪_⟫ c)) → f (τ P (⟪_ⓐ_⟫↑ c q)) == τ Q q
    ⟪_ⓐ_⟫↑= c q = ⟪_ⓐ_⟫↓= c (⟪_ⓐ_⟫↑ c q) ∙ ap (τ Q) (⟪_ⓐ_⟫⇅ c q)

    module _ {c : γ P j} where

      ⟪_⟫≃ : ρ P c ≃ ρ Q (⟪_⟫ c)
      ⟪_⟫≃ = ⟪_ⓐ_⟫≃ c

      ⟪_⟫↓ : ρ P c → ρ Q (⟪_⟫ c)
      ⟪_⟫↓ = –> ⟪_⟫≃

      ⟪_⟫↑ : ρ Q (⟪_⟫ c) → ρ P c
      ⟪_⟫↑ = <– ⟪_⟫≃

      ⟪_⟫⇵ : (p : ρ P c) → ⟪_⟫↑ (⟪_⟫↓ p)  == p
      ⟪_⟫⇵ = <–-inv-l ⟪_⟫≃

      ⟪_⟫⇅ : (q : ρ Q (⟪_⟫ c)) → ⟪_⟫↓ (⟪_⟫↑ q) == q
      ⟪_⟫⇅ = <–-inv-r ⟪_⟫≃

      ⟪_⟫-adj : (p : ρ P c) → ap (⟪_⟫↓) (⟪_⟫⇵ p) == ⟪_⟫⇅ (⟪_⟫↓ p)
      ⟪_⟫-adj = <–-inv-adj ⟪_⟫≃

      ⟪_⟫↓= : (p : ρ P c) → f (τ P p) == τ Q (⟪_⟫↓ p)
      ⟪_⟫↓= = τ-coh α {c = c}

      ⟪_⟫↑= : (q : ρ Q ⟪ c ⟫) → f (τ P (⟪_⟫↑ q)) == τ Q q
      ⟪ q ⟫↑= = (⟪_⟫↓= (⟪_⟫↑ q)) ∙ ap (τ Q) (⟪_⟫⇅ q)

      --
      -- The following says that for any q : p₀ == p₁,
      -- we have a commutative square :
      --
      --       f (τ P p₀)  ==  τ Q (⟪ α ⟫↓ p₁)
      --            ||                ||
      --            ||                ||
      --       f (τ P p₁)  ==  τ Q (⟪ α ⟫↓ p₁)
      --

      ⟪_⟫■ : {p₀ p₁ : ρ P c} (q : p₀ == p₁) →
             ! (ap (f ∘ τ P) q) ∙ ⟪_⟫↓= p₀ ∙ ap (τ Q) (ap (⟪_⟫↓) q) == ⟪_⟫↓= p₁
      ⟪_⟫■ idp = ∙-unit-r (⟪_⟫↓= _)

  module _ {ℓ} {I J K L : Type ℓ}
           {f : I → K} {g : J → L}
           {P : Poly I J} {Q : Poly K L} where

    -- A very general method for transferring decorations ...
    push : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧)
           (X : I → Type ℓ) (Y : K → Type ℓ)
           (T : {i : I} → X i → Y (f i))
           {j : J} {c : γ P j}
         → ⟦ P ⟧⟦ c ≺ X ⟧ → ⟦ Q ⟧⟦ ⟪ α ⟫ c ≺ Y ⟧
    push α X Y T φ q = transport Y (⟪ α ⟫↑= q) (T (φ (⟪ α ⟫↑ q)))

    push-coh : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧)
               (X : I → Type ℓ) (Y : K → Type ℓ)
               (T : {i : I} → X i → Y (f i))
               {j : J} {c : γ P j} (φ : ⟦ P ⟧⟦ c ≺ X ⟧) (p : ρ P c) →
               T (φ p) == push α X Y T φ (⟪ α ⟫↓ p) [ Y ↓ ⟪ α ⟫↓= p ]
    push-coh α X Y T φ p = from-transp Y (⟪ α ⟫↓= p) lemma where
      φ-expand : transport Y (! (ap (f ∘ τ P) (⟪ α ⟫⇵ p))) (T (φ p)) == T (φ (⟪ α ⟫↑ (⟪ α ⟫↓ p)))
      φ-expand = to-transp (!ᵈ (↓-ap-in Y (f ∘ τ P) (apd (T ∘ φ) (⟪ α ⟫⇵ p))))

      lemma = transport Y (⟪ α ⟫↓= p) (T (φ p))
                =⟨ ! (⟪ α ⟫■ (⟪ α ⟫⇵ p))|in-ctx (λ x → transport Y x (T (φ p))) ⟩
              transport Y (! (ap (f ∘ τ P) (⟪ α ⟫⇵ p)) ∙ ⟪ α ⟫↓= (⟪ α ⟫↑ (⟪ α ⟫↓ p)) ∙ ap (τ Q) (ap ⟪ α ⟫↓ (⟪ α ⟫⇵ p))) (T (φ p))
                =⟨ ⟪ α ⟫-adj p |in-ctx (λ x → transport Y (! (ap (f ∘ τ P) (⟪ α ⟫⇵ p)) ∙ ⟪ α ⟫↓= (⟪ α ⟫↑ (⟪ α ⟫↓ p)) ∙ ap (τ Q) x) (T (φ p))) ⟩
              transport Y (! (ap (f ∘ τ P) (⟪ α ⟫⇵ p)) ∙ (⟪ α ⟫↓= (⟪ α ⟫↑ (⟪ α ⟫↓ p)) ∙ ap (τ Q) (⟪ α ⟫⇅ (⟪ α ⟫↓ p)))) (T (φ p))
                =⟨ trans-∙ (! (ap (f ∘ τ P) (⟪ α ⟫⇵ p))) (⟪ α ⟫↑= (⟪ α ⟫↓ p)) (T (φ p)) ⟩
              transport Y (⟪ α ⟫↑= (⟪ α ⟫↓ p)) (transport Y (! (ap (f ∘ τ P) (⟪ α ⟫⇵ p))) (T (φ p)))
                =⟨ φ-expand |in-ctx (λ x → transport Y (⟪ α ⟫↑= (⟪ α ⟫↓ p)) x) ⟩
              transport Y (⟪ α ⟫↑= (⟪ α ⟫↓ p)) (T (φ (⟪ α ⟫↑ (⟪ α ⟫↓ p)))) ∎


    -- Specialized to the case where T is the identity, the above
    -- induces an equivalence on decorations
    ⟪_∣_⟫⇓ : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (X : K → Type ℓ) {j : J} {c : γ P j} →
            ⟦ P ⟧⟦ c ≺ X ∘ f ⟧ → ⟦ Q ⟧⟦ ⟪ α ⟫ c ≺ X ⟧
    ⟪ α ∣ X ⟫⇓ φ q = push α (X ∘ f) X (λ x → x) φ q

    ⟪_∣_⟫⇑ : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (X : K → Type ℓ) {j : J} {c : γ P j} →
            ⟦ Q ⟧⟦ ⟪ α ⟫ c ≺ X ⟧ → ⟦ P ⟧⟦ c ≺ X ∘ f ⟧
    ⟪ α ∣ X ⟫⇑ ψ p = transport X (! (⟪ α ⟫↓= p)) (ψ (⟪ α ⟫↓ p))

    -- ⟪_∣_⟫⇓-po : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (X : K → Type ℓ) {j : J} {c : γ P j}
    --            (φ : ⟦ P ⟧⟦ c ≺ X ∘ f ⟧) (q : ρ Q (⟪ α ⟫ c)) →
    --              φ (⟪ α ⟫↑ q) == ⟪ α ∣ X ⟫⇓ φ q [ X ↓ (⟪ α ⟫↑= q) ]
    -- ⟪ α ∣ X ⟫⇓-po φ q = from-transp X (⟪ α ⟫↑= q) idp

    -- ⟪_∣_⟫⇑-po : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (X : K → Type ℓ) {j : J} {c : γ P j}
    --            (ψ : ⟦ Q ⟧⟦ ⟪ α ⟫ c ≺ X ⟧) (p : ρ P c) →
    --            ⟪ α ∣ X ⟫⇑ ψ p == ψ (⟪ α ⟫↓ p) [ X ↓ ⟪ α ⟫↓= p ]
    -- ⟪ α ∣ X ⟫⇑-po ψ p = from-transp X (⟪ α ⟫↓= p) {!idp!} -- (trans-move-left (⟪ α ⟫↓= p) idp)

    -- A version of the previous, parameterized over a path
    -- ⟪_∣_↓_⟫⇑ : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (X : K → Type ℓ)
    --           {j : J} {c : γ P j} {d : γ Q (g j)}
    --           (r : ⟪ α ⟫ c == d) →
    --           ⟦ Q ⟧⟦ d ≺ X ⟧ → ⟦ P ⟧⟦ c ≺ X ∘ f ⟧
    -- ⟪ α ∣ X ↓ idp ⟫⇑ ψ = ⟪ α ∣ X ⟫⇑ ψ

  --   -- Another path parameterized version, though this is getting a bit messy ...
  --   ⟪_∣_↓_⟫⇑-po : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (X : K → Type ℓ)
  --                {j : J} {c : γ P j} {d : γ Q (g j)} →
  --                (r : ⟪ α ⟫ c == d) (ψ : ⟦ Q ⟧⟦ d ≺ X ⟧) (p : ρ P c) →
  --                ⟪ α ∣ X ↓ r ⟫⇑ ψ p == ψ (⟦ Q ↓ r ⟧↓ ( ⟪ α ⟫↓ p)) [ X ↓ ⟪ α ⟫↓= p ∙ ⟦ Q ↓ r ⟧↓= (⟪ α ⟫↓ p) ]
  --   ⟪ α ∣ X ↓ idp ⟫⇑-po ψ p = transport (λ x → PathOver X x (⟪ α ∣ X ⟫⇑ ψ p) (ψ (⟪ α ⟫↓ p))) (! (∙-unit-r (⟪ α ⟫↓= p)))
  --                               (⟪ α ∣ X ⟫⇑-po ψ p)

    ⟪_∣_⟫⇓-coh : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (X : K → Type ℓ) {j : J} {c : γ P j}
                (φ : ⟦ P ⟧⟦ c ≺ X ∘ f ⟧) (p : ρ P c) →
                 φ p == ⟪ α ∣ X ⟫⇓ φ (⟪ α ⟫↓ p) [ X ↓ ⟪ α ⟫↓= p ]
    ⟪ α ∣ X ⟫⇓-coh φ = push-coh α (X ∘ f) X (λ x → x) φ

    ⟪_∣_⟫⇑-coh : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (X : K → Type ℓ) {j : J} {c : γ P j}
                (ψ : ⟦ Q ⟧⟦ ⟪ α ⟫ c ≺ X ⟧) (q : ρ Q (⟪ α ⟫ c)) →
                 ψ q == ⟪ α ∣ X ⟫⇑ ψ (⟪ α ⟫↑ q) [ X ↓ ! (⟪ α ⟫↑= q) ]
    ⟪ α ∣ X ⟫⇑-coh ψ q = from-transp X (! (⟪ α ⟫↑= q)) lemma where
      ψ-expand : transport X (! (ap (τ Q) (⟪ α ⟫⇅ q))) (ψ q) == (ψ (⟪ α ⟫↓ (⟪ α ⟫↑ q)))
      ψ-expand = to-transp (!ᵈ (↓-ap-in X (τ Q) (apd ψ (⟪ α ⟫⇅ q))))

      lemma = transport X (! (⟪ α ⟫↓= (⟪ α ⟫↑ q) ∙ ap (τ Q) (⟪ α ⟫⇅ q))) (ψ q)
                =⟨ !-∙ (⟪ α ⟫↓= (⟪ α ⟫↑ q)) (ap (τ Q) (⟪ α ⟫⇅ q))  |in-ctx (λ x → transport X x (ψ q)) ⟩
              transport X ((! (ap (τ Q) (⟪ α ⟫⇅ q))) ∙ (! (⟪ α ⟫↓= (⟪ α ⟫↑ q)))) (ψ q)
                =⟨ trans-∙ ((! (ap (τ Q) (⟪ α ⟫⇅ q)))) ((! (⟪ α ⟫↓= (⟪ α ⟫↑ q)))) (ψ q) ⟩
              transport X (! (⟪ α ⟫↓= (⟪ α ⟫↑ q))) (transport X (! (ap (τ Q) (⟪ α ⟫⇅ q))) (ψ q))
                =⟨ ψ-expand |in-ctx (λ x → transport X (! (⟪ α ⟫↓= (⟪ α ⟫↑ q))) x) ⟩  -- expand ψ
              ⟪ α ∣ X ⟫⇑ ψ (⟪ α ⟫↑ q) ∎

    ⟪_∣_⟫⇕-l : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (X : K → Type ℓ) {j : J} {c : γ P j}
              (φ : ⟦ P ⟧⟦ c ≺ X ∘ f ⟧) (p : ρ P c) →
               ⟪ α ∣ X ⟫⇑ (⟪ α ∣ X ⟫⇓ φ) p == φ p
    ⟪ α ∣ X ⟫⇕-l φ p = ! (transport (λ x → φ p == ⟪ α ∣ X ⟫⇑ (⟪ α ∣ X ⟫⇓ φ) p [ X ↓ x ]) po-path-is-id po-lemma) where
      po-path : f (τ P p) == f (τ P p)
      po-path = ⟪ α ⟫↓= p ∙ ! (⟪ α ⟫↓= (⟪ α ⟫↑ (⟪ α ⟫↓ p)) ∙ ap (τ Q) (⟪ α ⟫⇅ (⟪ α ⟫↓ p))) ∙ ap (f ∘ τ P) (⟪ α ⟫⇵ p)

      po-lemma : φ p == ⟪ α ∣ X ⟫⇑ (⟪ α ∣ X ⟫⇓ φ) p [ X ↓ po-path ]
      po-lemma = ⟪ α ∣ X ⟫⇓-coh φ p ∙ᵈ
                 ⟪ α ∣ X ⟫⇑-coh (⟪ α ∣ X ⟫⇓ φ) (⟪ α ⟫↓ p) ∙ᵈ
                 ↓-ap-in X (f ∘ τ P) (apd (⟪ α ∣ X ⟫⇑ (⟪ α ∣ X ⟫⇓ φ)) (⟪ α ⟫⇵ p))

      po-path-is-id : po-path == idp
      po-path-is-id = ⟪ α ⟫↓= p ∙ ! (⟪ α ⟫↓= (⟪ α ⟫↑ (⟪ α ⟫↓ p)) ∙ ap (τ Q) (⟪ α ⟫⇅ (⟪ α ⟫↓ p))) ∙ ap (f ∘ τ P) (⟪ α ⟫⇵ p)
                        =⟨ ! (!-! (ap (f ∘ τ P) (⟪ α ⟫⇵ p))) |in-ctx (λ x → ⟪ α ⟫↓= p ∙ ! (⟪ α ⟫↓= (⟪ α ⟫↑ (⟪ α ⟫↓ p)) ∙ ap (τ Q) (⟪ α ⟫⇅ (⟪ α ⟫↓ p))) ∙ x) ⟩
                      ⟪ α ⟫↓= p ∙ ! (⟪ α ⟫↓= (⟪ α ⟫↑ (⟪ α ⟫↓ p)) ∙ ap (τ Q) (⟪ α ⟫⇅ (⟪ α ⟫↓ p))) ∙ ! (! (ap (f ∘ τ P) (⟪ α ⟫⇵ p)))
                        =⟨ ∙-! (⟪ α ⟫↓= (⟪ α ⟫↑ (⟪ α ⟫↓ p)) ∙ ap (τ Q) (⟪ α ⟫⇅ (⟪ α ⟫↓ p))) (! (ap (f ∘ τ P) (⟪ α ⟫⇵ p))) |in-ctx (λ x → ⟪ α ⟫↓= p ∙ x) ⟩
                      ⟪ α ⟫↓= p ∙ ! (! (ap (f ∘ τ P) (⟪ α ⟫⇵ p)) ∙ ⟪ α ⟫↓= (⟪ α ⟫↑ (⟪ α ⟫↓ p)) ∙ ap (τ Q) (⟪ α ⟫⇅ (⟪ α ⟫↓ p)))
                        =⟨ ! (⟪ α ⟫-adj p) |in-ctx (λ x → ⟪ α ⟫↓= p ∙ ! (! (ap (f ∘ τ P) (⟪ α ⟫⇵ p)) ∙ ⟪ α ⟫↓= (⟪ α ⟫↑ (⟪ α ⟫↓ p)) ∙ ap (τ Q) x)) ⟩
                      ⟪ α ⟫↓= p ∙ ! (! (ap (f ∘ τ P) (⟪ α ⟫⇵ p)) ∙ ⟪ α ⟫↓= (⟪ α ⟫↑ (⟪ α ⟫↓ p)) ∙ ap (τ Q) (ap (⟪ α ⟫↓) (⟪ α ⟫⇵ p)))
                        =⟨ ⟪ α ⟫■ (⟪ α ⟫⇵ p) |in-ctx (λ x → ⟪ α ⟫↓= p ∙ ! x) ⟩
                      ⟪ α ⟫↓= p ∙ ! (⟪ α ⟫↓= p)
                        =⟨ !-inv-r (⟪ α ⟫↓= p) ⟩
                      idp ∎

    ⟪_∣_⟫⇕-r : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (X : K → Type ℓ) {j : J} {c : γ P j}
              (ψ : ⟦ Q ⟧⟦ ⟪ α ⟫ c ≺ X ⟧) (q : ρ Q ( ⟪ α ⟫ c)) →
               ⟪ α ∣ X ⟫⇓ (⟪ α ∣ X ⟫⇑ ψ) q == ψ q
    ⟪ α ∣ X ⟫⇕-r ψ q = ! (transport (λ x → ψ q == ⟪ α ∣ X ⟫⇓ (⟪ α ∣ X ⟫⇑ ψ) q [ X ↓ x ]) po-path-is-id po-lemma) where
      po-path : τ Q q == τ Q q
      po-path = ! (⟪ α ⟫↑= q) ∙ ⟪ α ⟫↓= (⟪ α ⟫↑ q) ∙ ap (τ Q) (⟪ α ⟫⇅ q)

      po-lemma : ψ q == ⟪ α ∣ X ⟫⇓ (⟪ α ∣ X ⟫⇑ ψ) q [ X ↓ po-path ]
      po-lemma = ⟪ α ∣ X ⟫⇑-coh ψ q ∙ᵈ
                 ⟪ α ∣ X ⟫⇓-coh (⟪ α ∣ X ⟫⇑ ψ) (⟪ α ⟫↑ q) ∙ᵈ
                 ↓-ap-in X (τ Q) (apd (⟪ α ∣ X ⟫⇓ (⟪ α ∣ X ⟫⇑ ψ)) (⟪ α ⟫⇅ q))

      po-path-is-id : po-path == idp
      po-path-is-id = ! (⟪ α ⟫↓= (⟪ α ⟫↑ q) ∙ ap (τ Q) (⟪ α ⟫⇅ q)) ∙ ⟪ α ⟫↓= (⟪ α ⟫↑ q) ∙ ap (τ Q) (⟪ α ⟫⇅ q)
                        =⟨ !-∙ (⟪ α ⟫↓= (⟪ α ⟫↑ q)) (ap (τ Q) (⟪ α ⟫⇅ q)) |in-ctx (λ x → x ∙ ⟪ α ⟫↓= (⟪ α ⟫↑ q) ∙ ap (τ Q) (⟪ α ⟫⇅ q)) ⟩
                      (! (ap (τ Q) (⟪ α ⟫⇅ q)) ∙ ! (⟪ α ⟫↓= (⟪ α ⟫↑ q))) ∙ ⟪ α ⟫↓= (⟪ α ⟫↑ q) ∙ ap (τ Q) (⟪ α ⟫⇅ q)
                        =⟨ ∙-assoc (! (ap (τ Q) (⟪ α ⟫⇅ q))) (! (⟪ α ⟫↓= (⟪ α ⟫↑ q))) (⟪ α ⟫↓= (⟪ α ⟫↑ q) ∙ ap (τ Q) (⟪ α ⟫⇅ q)) ⟩
                      ! (ap (τ Q) (⟪ α ⟫⇅ q)) ∙ ! (⟪ α ⟫↓= (⟪ α ⟫↑ q)) ∙ ⟪ α ⟫↓= (⟪ α ⟫↑ q) ∙ ap (τ Q) (⟪ α ⟫⇅ q)
                        =⟨ ! (∙-assoc (! (⟪ α ⟫↓= (⟪ α ⟫↑ q))) (⟪ α ⟫↓= (⟪ α ⟫↑ q)) (ap (τ Q) (⟪ α ⟫⇅ q))) |in-ctx (λ x → ! (ap (τ Q) (⟪ α ⟫⇅ q)) ∙ x) ⟩
                      ! (ap (τ Q) (⟪ α ⟫⇅ q)) ∙ (! (⟪ α ⟫↓= (⟪ α ⟫↑ q)) ∙ ⟪ α ⟫↓= (⟪ α ⟫↑ q)) ∙ ap (τ Q) (⟪ α ⟫⇅ q)
                        =⟨ !-inv-l (⟪ α ⟫↓= (⟪ α ⟫↑ q)) |in-ctx (λ x → ! (ap (τ Q) (⟪ α ⟫⇅ q)) ∙ x ∙ ap (τ Q) (⟪ α ⟫⇅ q)) ⟩
                      ! (ap (τ Q) (⟪ α ⟫⇅ q)) ∙ ap (τ Q) (⟪ α ⟫⇅ q)
                        =⟨ !-inv-l (ap (τ Q) (⟪ α ⟫⇅ q)) ⟩
                      idp ∎

    ⟪_∣_⟫⇕-eqv : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (X : K → Type ℓ) {j : J} {c : γ P j} →
                 ⟦ P ⟧⟦ c ≺ X ∘ f ⟧ ≃ ⟦ Q ⟧⟦ ⟪ α ⟫ c ≺ X ⟧
    ⟪ α ∣ X ⟫⇕-eqv = equiv ⟪ α ∣ X ⟫⇓ ⟪ α ∣ X ⟫⇑ (λ ψ → λ= (⟪ α ∣ X ⟫⇕-r ψ)) (λ φ → λ= (⟪ α ∣ X ⟫⇕-l φ))

  -- Vertical composition
  module _ {ℓ} {I J K L M N : Type ℓ}
           {f : I → K} {g : J → L}
           {h : K → M} {k : L → N}
           {P : Poly I J} {Q : Poly K L} {R : Poly M N} where

    infixr 50 _▶_

    _▶_ : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (β : ⟦ h ∣ k ⟧⟦ Q ⇒ R ⟧) → ⟦ h ∘ f ∣ k ∘ g ⟧⟦ P ⇒ R ⟧
    γ-map (α ▶ β) = ⟪ β ⟫ ∘ ⟪ α ⟫
    ρ-eqv (α ▶ β) = ⟪ β ⟫≃ ∘e ⟪ α ⟫≃
    τ-coh (α ▶ β) p = (ap h (⟪ α ⟫↓= p)) ∙ ⟪ β ⟫↓= (⟪ α ⟫↓ p)

  -- Horizontal composition
  module _ {ℓ} {I J K L M N : Type ℓ}
           {f : I → L} {g : J → M} {h : K → N}
           {P : Poly I J} {R : Poly J K}
           {Q : Poly L M} {S : Poly M N}  where

    -- With the very general "push" method above, these versions for
    -- horizontal composition become special cases.

    ⟪_∣_⟫⇕ : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (β : ⟦ g ∣ h ⟧⟦ R ⇒ S ⟧) {k : K} {c : γ R k} →
            ⟦ R ⟧⟦ c ≺ γ P ⟧ → ⟦ S ⟧⟦ ⟪ β ⟫ c ≺ γ Q ⟧
    ⟪ α ∣ β ⟫⇕ φ = push β (γ P) (γ Q) ⟪ α ⟫ φ

    ⟪_∣_⟫⇕-coh : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (β : ⟦ g ∣ h ⟧⟦ R ⇒ S ⟧) {k : K} {c : γ R k} →
                (φ : ⟦ R ⟧⟦ c ≺ γ P ⟧) (p : ρ R c) →
                ⟪ α ⟫ (φ p) == ⟪ α ∣ β ⟫⇕ φ (⟪ β ⟫↓ p) [ γ Q ↓ ⟪ β ⟫↓= p ]
    ⟪ α ∣ β ⟫⇕-coh φ = push-coh β (γ P) (γ Q) ⟪ α ⟫ φ

    infixr 40 _∥_

    _∥_ : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (β : ⟦ g ∣ h ⟧⟦ R ⇒ S ⟧) → ⟦ f ∣ h ⟧⟦ P ⊚ R ⇒ Q ⊚ S ⟧
    γ-map (α ∥ β) (c , φ) = ⟪ β ⟫ c , ⟪ α ∣ β ⟫⇕ φ
    ρ-eqv (α ∥ β) {_} {c , φ} = equiv-Σ' ⟪ β ⟫≃ (λ p → ⟦ Q ↓ ⟪ α ∣ β ⟫⇕-coh φ p ⟧≃ ∘e ⟪ α ⟫≃)
    τ-coh (α ∥ β) {_} {c , φ} (p₀ , p₁) = ⟪ α ⟫↓= p₁ ∙ ⟦ Q ↓ ⟪ α ∣ β ⟫⇕-coh φ p₀ ⟧↓= (⟪ α ⟫↓ p₁)

  module _ {ℓ} {I J K L : Type ℓ}
           {f : I → K} {g : J → L}
           {P : Poly I J} {Q : Poly K L} where

    record LocalEqv (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (β : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) {j : J} (c : γ P j) : Type ℓ where
      constructor lcl-eqv
      field
        γ≈ : ⟪ α ⟫ c == ⟪ β ⟫ c
        ρ≈ : (p : ρ P c) → ⟪ α ⟫↓ p == ⟪ β ⟫↓ p [ ρ Q ↓ γ≈ ]
        τ≈ : (p : ρ P c) → ⟪ α ⟫↓= p == ⟪ β ⟫↓= p [ (λ cp → f (τ P p) == τ Q (snd cp)) ↓ pair= γ≈ (ρ≈ p) ]

    open LocalEqv public

    _≈_ⓐ_ : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (β : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) {j : J} (c : γ P j) → Type ℓ
    α ≈ β ⓐ c = LocalEqv α β c

    _≈_ : (α : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) (β : ⟦ f ∣ g ⟧⟦ P ⇒ Q ⟧) → Type ℓ
    α ≈ β = {j : J} → (c : γ P j) → α ≈ β ⓐ c
