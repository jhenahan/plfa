module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)

-- Definitions

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-trans′ : ∀ (m n p : ℕ)
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans′ zero    _       _       z≤n       _         = z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans′ m n p m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n       = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ----------
    → Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ----------
    → Total′ m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n    = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n       = forward z≤n
≤-total′ (suc m) zero    = flipped z≤n
≤-total′ (suc m) (suc n) = helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n) = forward (s≤s m≤n)
  helper (flipped n≤m) = flipped (s≤s n≤m)

≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m       zero    = flipped z≤n
≤-total″ zero    (suc n) = forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)


-- Examples

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

-- Exercises


-- Exercise `orderings`

-- Preorder that is not a partial order
-- {a, b} → {(a, a), (a, b), (b, a), (b, b)}
-- Reflexive: (a, a); (b, b)
-- Transitive: (a, b), (b, a) ⇒ (a, a)

-- Partial order that is not a total order
-- Subsets of {0, 1} under ⊂: {∅, {0}, {1}, {0, 1}}
-- Reflexive: A ⊂ A
-- Transitive: A ⊂ B, B ⊂ C ⇒ A ⊂ C
-- Anti-symmetric: A ⊂ B, B ⊂ A ⇒ A ≡ B

-- Exercise `≤-antisym-cases`

-- We omit cases in `≤-antisym` where one argument is `z≤n` and one is
-- `s≤s` because (WLOG) given evidence that `zero ≤ n` and `n ≤ zero`,
-- we must conclude that `n ≡ 0` because `suc n ≤ suc zero`.

-- Exercise `*-mono-≤`

*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n * p ≤ n * q
*-monoʳ-≤ zero    p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

-- Exercise `<-trans`

<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans z<s       (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

-- Exercise `trichotomy`

data Trichotomous (m n : ℕ) : Set where

  less :
      m < n
      ---------
    → Trichotomous m n

  same :
      m ≡ n
      ---------
    → Trichotomous m n

  more :
      n < m
      ---------
    → Trichotomous m n

<-trichotomous : ∀ {m n : ℕ} → Trichotomous m n
<-trichotomous {zero} {zero} = same refl
<-trichotomous {zero} {suc n} = less z<s
<-trichotomous {suc m} {zero} = more z<s
<-trichotomous {suc m} {suc n} with <-trichotomous {m} {n}
...                            | less m<n = less (s<s m<n)
...                            | same m≡n = same (cong suc m≡n)
...                            | more m>n = more (s<s m>n)

-- Exercise `+-mono-<`

+-monoʳ-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoʳ-< m p q p<q) (+-monoˡ-< m n q m<n)

-- Exercise `≤-iff-<`

suc≤-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
suc≤-< (s≤s z≤n) = z<s
suc≤-< (s≤s (s≤s m≤n)) = s<s (suc≤-< (s≤s m≤n))

<-suc≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-suc≤ z<s = s≤s z≤n
<-suc≤ (s<s m<n) = s≤s (<-suc≤ m<n)

suc≤-≤ : ∀ {m n : ℕ} → suc m ≤ n → m ≤ n
suc≤-≤ (s≤s z≤n) = z≤n
suc≤-≤ (s≤s (s≤s m≤n)) = s≤s (suc≤-≤ (s≤s m≤n))

-- Exercise `<-trans-revisited`

<-trans-revisited : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans-revisited m<n n<p = suc≤-< (≤-trans (<-suc≤ m<n) (suc≤-≤ (<-suc≤ n<p)))

-- Exercise `o+o≡e`

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e (suc zero) (suc zero) = suc (suc zero)
o+o≡e (suc zero) (suc (suc on)) = suc (suc (suc on))
o+o≡e (suc (suc om)) (suc zero) = suc (suc (o+o≡e om (suc zero)))
o+o≡e (suc (suc om)) (suc (suc on)) = suc (suc (o+o≡e om (suc (suc on))))

-- Exercise `Bin-predicates`
-- See `./Binary.agda`
