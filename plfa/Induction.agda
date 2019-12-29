module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

-- Definitions

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p ≡⟨⟩
    n + p          ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p   ≡⟨⟩
    suc (m + n) + p   ≡⟨⟩
    suc ((m + n) + p) ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p)) ≡⟨⟩
    suc m + (n + p)
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          = refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  = refl

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero   ≡⟨⟩
    suc (m + zero) ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n ≡⟨⟩
    suc n        ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n     ≡⟨⟩
    suc (m + suc n)   ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n)) ≡⟨⟩
    suc (suc m + n)
  ∎

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero ≡⟨ +-identityʳ m ⟩
    m        ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n   ≡⟨ +-suc m n ⟩
    suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m) ≡⟨⟩
    suc n + m
  ∎

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q) ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q)) ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q) ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

-- Examples

3+4+5-assoc : (3 + 4) + 5 ≡ 3 + (4 + 5)
3+4+5-assoc =
  begin
    (3 + 4) + 5 ≡⟨⟩
    7 + 5       ≡⟨⟩
    12          ≡⟨⟩
    3 + 9       ≡⟨⟩
    3 + (4 + 5)
  ∎

-- Exercises

-- Exercise `operators`

data Bool : Set where
  T : Bool
  F : Bool

_∧_ : Bool → Bool → Bool
T ∧ b = b
F ∧ _ = F

_∨_ : Bool → Bool → Bool
F ∨ b = b
T ∨ _ = T

infixr 6 _∧_
infixr 5 _∨_

∧-identityₗ : ∀ (b : Bool) → T ∧ b ≡ b
∧-identityₗ _ = refl

∧-identityᵣ : ∀ (b : Bool) → b ∧ T ≡ b
∧-identityᵣ T = refl
∧-identityᵣ F = refl

∧-zeroₗ : ∀ (b : Bool) → F ∧ b ≡ F
∧-zeroₗ _ = refl

∧-zeroᵣ : ∀ (b : Bool) → b ∧ F ≡ F
∧-zeroᵣ T = refl
∧-zeroᵣ F = refl

∧-assoc : ∀ (a b c : Bool) → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
∧-assoc T b c =
  begin
    (T ∧ b) ∧ c ≡⟨ ∧-identityₗ ((T ∧ b) ∧ c) ⟩
    b ∧ c       ≡⟨ sym (∧-identityₗ (b ∧ c)) ⟩
    T ∧ (b ∧ c)
  ∎
∧-assoc F b c =
  begin
    (F ∧ b) ∧ c ≡⟨ ∧-zeroₗ b ⟩
    F ∧ c       ≡⟨ ∧-zeroₗ c ⟩
    F           ≡⟨ sym (∧-zeroₗ (b ∧ c)) ⟩
    F ∧ (b ∧ c)
  ∎


∧-comm : ∀ (a b : Bool) → a ∧ b ≡ b ∧ a
∧-comm T b =
  begin
    T ∧ b ≡⟨ ∧-identityₗ b ⟩
    b     ≡⟨ sym (∧-identityᵣ b) ⟩
    b ∧ T
  ∎
∧-comm F b =
  begin
    F ∧ b ≡⟨ ∧-zeroₗ b ⟩
    F     ≡⟨ sym (∧-zeroᵣ b) ⟩
    b ∧ F
  ∎

∨-identityₗ : ∀ (b : Bool) → F ∨ b ≡ b
∨-identityₗ _ = refl

∨-identityᵣ : ∀ (b : Bool) → b ∨ F ≡ b
∨-identityᵣ T = refl
∨-identityᵣ F = refl

∨-zeroₗ : ∀ (b : Bool) → T ∨ b ≡ T
∨-zeroₗ _ = refl

∨-zeroᵣ : ∀ (b : Bool) → b ∨ T ≡ T
∨-zeroᵣ T = refl
∨-zeroᵣ F = refl

∨-assoc : ∀ (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
∨-assoc T b c = refl
∨-assoc F b c = refl

∨-comm : ∀ (a b : Bool) → a ∨ b ≡ b ∨ a
∨-comm T b = sym (∨-zeroᵣ b)
∨-comm F b = sym (∨-identityᵣ b)

∨-distribˡ-∧ : ∀ (a b c : Bool) → a ∨ (b ∧ c) ≡ (a ∨ b) ∧ (a ∨ c)
∨-distribˡ-∧ T b c = refl
∨-distribˡ-∧ F b c = refl

∧-distribˡ-∨ : ∀ (a b c : Bool) → a ∧ (b ∨ c) ≡ (a ∧ b) ∨ (a ∧ c)
∧-distribˡ-∨ T b c = refl
∧-distribˡ-∨ F b c = refl


-- Function composition has identity and is associative, but is not commutative
--| Identity: id
--| Associative: f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
--| Not commutative: f ∘ g ≢ g ∘ f

-- Exercise `+-swap`

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p) ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

-- Exercise `*-distrib-+`

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero    n p = refl
*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p       ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)   ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + m * p) + (n * p) ≡⟨⟩
    suc m * p + n * p
  ∎

-- Exercise `*-assoc`

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero    n p = refl
*-assoc (suc m) n p =
  begin
    (suc m * n) * p     ≡⟨⟩
    (n + m * n) * p     ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + m * n * p   ≡⟨ cong (n * p +_) (*-assoc m n p) ⟩
    n * p + m * (n * p) ≡⟨⟩
    suc m * (n * p)
  ∎

-- Exercise `*-comm`

*-zero : ∀ (n : ℕ) → zero ≡ n * zero
*-zero zero    = refl
*-zero (suc n) = *-zero n

*-identity : ∀ (n : ℕ) → n * 1 ≡ n
*-identity zero    = refl
*-identity (suc n) = cong suc (*-identity n)

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero    n = refl
*-suc (suc m) n =
  begin
    suc m * suc n         ≡⟨⟩
    suc n + m * suc n     ≡⟨ cong (suc n +_) (*-suc m n) ⟩
    suc n + (m + m * n)   ≡⟨⟩
    suc (n + (m + m * n)) ≡⟨ cong suc (+-swap n m (m * n)) ⟩
    suc (m + (n + m * n)) ≡⟨⟩
    suc m + suc m * n
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero    n = *-zero n
*-comm (suc m) n =
  begin
    suc m * n ≡⟨⟩
    n + m * n ≡⟨ cong (n +_) (*-comm m n) ⟩
    n + n * m ≡⟨ sym (*-suc n m) ⟩
    n * suc m
  ∎

-- Exercise `0∸n≡0`

0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero    = refl
0∸n≡0 (suc n) = refl

-- Exercise `∸-+-assoc`

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero    zero    _ = refl
∸-+-assoc zero    (suc n) p = 0∸n≡0 p
∸-+-assoc (suc m) zero    _ = refl
∸-+-assoc (suc m) (suc n) p = ∸-+-assoc m n p

-- Exercise `+*^`

^-identityʳ : ∀ (n : ℕ) → n ^ 1 ≡ n
^-identityʳ zero    = refl
^-identityʳ (suc n) = cong suc (^-identityʳ n)

*-identityʳ : ∀ (n : ℕ) → n * 1 ≡ n
*-identityʳ zero    = refl
*-identityʳ (suc n) = cong suc (*-identityʳ n)

*-identityˡ : ∀ (n : ℕ) → 1 * n ≡ n
*-identityˡ n = +-identityʳ n

^-zeroˡ : ∀ (n : ℕ) → 1 ^ n ≡ 1
^-zeroˡ zero    = refl
^-zeroˡ (suc n) =
  begin
    1 ^ suc n   ≡⟨⟩
    1 * (1 ^ n) ≡⟨ *-identityˡ (1 ^ n) ⟩
    1 ^ n       ≡⟨ ^-zeroˡ n ⟩
    1
  ∎

^-zeroʳ : ∀ (n : ℕ) → n ^ 0 ≡ 1
^-zeroʳ n = refl

*-swap : ∀ (m n p : ℕ) → m * (n * p) ≡ n * (m * p)
*-swap m n p =
  begin
    m * (n * p) ≡⟨ sym (*-assoc m n p) ⟩
    m * n * p ≡⟨ cong (_* p) (*-comm m n) ⟩
    n * m * p ≡⟨ *-assoc n m p ⟩
    n * (m * p)
  ∎

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero    p = sym (+-identityʳ (m ^ p))
^-distribˡ-+-* m (suc n) p =
  begin
    (m ^ (suc n + p))       ≡⟨⟩
    m * (m ^ (n + p))       ≡⟨ cong (m *_) (^-distribˡ-+-* m n p) ⟩
    m * ((m ^ n) * (m ^ p)) ≡⟨ sym (*-assoc m _ _) ⟩
    m * (m ^ n) * (m ^ p)   ≡⟨⟩
    (m ^ suc n) * (m ^ p)
  ∎

^-distribʳ-*-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-*-* m n zero = refl
^-distribʳ-*-* m n (suc p) =
  begin
    (m * n) ^ suc p               ≡⟨⟩
    m * n * ((m * n) ^ p)         ≡⟨ cong (m * n *_) (^-distribʳ-*-* m n p) ⟩
    m * n * ((m ^ p) * (n ^ p))   ≡⟨ *-assoc m n ((m ^ p) * (n ^ p)) ⟩
    m * (n * ((m ^ p) * (n ^ p))) ≡⟨ cong (m *_) (*-swap n (m ^ p) (n ^ p)) ⟩
    m * ((m ^ p) * (n * (n ^ p))) ≡⟨ sym (*-assoc m (m ^ p) (n * (n ^ p))) ⟩
    m * (m ^ p) * (n * (n ^ p))   ≡⟨⟩
    (m ^ suc p) * (n ^ suc p)
  ∎

^-distribˡ-*-^ : ∀ (m n p : ℕ) → m ^ (n * p) ≡ (m ^ n) ^ p
^-distribˡ-*-^ m n zero =
  begin
    m ^ (n * zero) ≡⟨ cong (m ^_) (sym (*-zero n)) ⟩
    m ^ zero       ≡⟨ ^-zeroʳ n ⟩
    1              ≡⟨ sym (^-zeroʳ (m ^ n)) ⟩
    (m ^ n) ^ zero
  ∎
^-distribˡ-*-^ m n (suc p) =
  begin
    m ^ (n * suc p)         ≡⟨ cong (m ^_) (*-suc n p) ⟩
    m ^ (n + n * p)         ≡⟨ ^-distribˡ-+-* m n (n * p) ⟩
    (m ^ n) * (m ^ (n * p)) ≡⟨ cong ((m ^ n) *_) (^-distribˡ-*-^ m n p) ⟩
    (m ^ n) * ((m ^ n) ^ p) ≡⟨⟩
    (m ^ n) ^ suc p
  ∎

-- Exercise: `Bin-laws`
-- See `./Binary.agda`
