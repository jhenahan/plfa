module plfa.Equality where



-- Exercises

-- Exercise `≤-Reasoning`

open import plfa.Relations using (_≤_; z≤n; s≤s; ≤-trans; ≤-refl)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

module ≤-Reasoning where

  infix  1 begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  begin x≤y = x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
      -----
    → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

  _∎ : ∀ (x : ℕ)
      -----
    → x ≤ x
  x ∎ = ≤-refl

open ≤-Reasoning

+-monoʳ-≤ : ∀ {n p q : ℕ}
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ {zero} p≤q = p≤q
+-monoʳ-≤ {suc n} {p} {q} p≤q =
  begin
    suc n + p   ≤⟨⟩
    suc (n + p) ≤⟨ s≤s (+-monoʳ-≤ p≤q) ⟩
    suc (n + q) ≤⟨⟩
    suc n + q
  ∎


≡-implies-≤ : ∀ {m n : ℕ} → m ≡ n → m ≤ n
≡-implies-≤ m≡n rewrite m≡n = ≤-refl

+-monoˡ-≤ : ∀ {m n p : ℕ}
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ {m} {n} {p} m≤n =
  begin
    m + p ≤⟨ ≡-implies-≤ (+-comm m p) ⟩
    p + m ≤⟨ +-monoʳ-≤ m≤n ⟩
    p + n ≤⟨ ≡-implies-≤ (+-comm p n) ⟩
    n + p
  ∎

+-mono-≤ : ∀ {m n p q : ℕ}
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ {m} {n} {p} {q} m≤n p≤q =
  begin
    m + p ≤⟨ +-monoʳ-≤ p≤q ⟩
    m + q ≤⟨ +-monoˡ-≤ m≤n ⟩
    n + q
  ∎

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
