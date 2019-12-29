module plfa.Binary where

import Data.Nat as Nat
open Nat using (ℕ; _*_; _+_; zero; suc)
open import Function using (_∘_)
open import Data.Nat.Properties using (+-suc; +-comm; +-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; inspect; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ =
  begin
    inc (⟨⟩ I O I I)
  ≡⟨⟩
    (inc (⟨⟩ I O I)) O
  ≡⟨⟩
    (inc (⟨⟩ I O)) O O
  ≡⟨⟩
    ⟨⟩ I I O O
  ∎

inc-4 : inc (inc (inc (inc ⟨⟩))) ≡ ⟨⟩ I O O
inc-4 =
  begin
    inc (inc (inc (inc ⟨⟩)))
  ≡⟨⟩
    inc (inc (inc (⟨⟩ I)))
  ≡⟨⟩
    inc (inc ((inc ⟨⟩) O))
  ≡⟨⟩
    inc (inc (⟨⟩ I O))
  ≡⟨⟩
    inc (⟨⟩ I I)
  ≡⟨⟩
    (inc (⟨⟩ I)) O
  ≡⟨⟩
    (inc ⟨⟩) O O
  ≡⟨⟩
    ⟨⟩ I O O
  ∎

to   : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = 2 * from b
from (b I) = suc (2 * from b)

_ : to 4 ≡ ⟨⟩ I O O
_ =
  begin
    to 4
  ≡⟨⟩
    to (suc 3)
  ≡⟨⟩
    inc (to 3)
  ≡⟨⟩
    inc (to (suc 2))
  ≡⟨⟩
    inc (inc (to (suc 1)))
  ≡⟨⟩
    inc (inc (inc (to (suc 0))))
  ≡⟨⟩
    inc (inc (inc (inc (to zero))))
  ≡⟨⟩
    inc (inc (inc (inc ⟨⟩)))
  ≡⟨ inc-4 ⟩
    ⟨⟩ I O O
  ∎

_ : from (⟨⟩ I O O) ≡ 4
_ =
  begin
    from (⟨⟩ I O O)
  ≡⟨⟩
    2 * from (⟨⟩ I O)
  ≡⟨⟩
    4 * from (⟨⟩ I)
  ≡⟨⟩
    4 * (suc (2 * from ⟨⟩))
  ≡⟨⟩
    4 * (suc (2 * zero))
  ≡⟨⟩
    4 * (suc zero)
  ≡⟨⟩
    4 * 1
  ≡⟨⟩
    4
  ∎

-- Exercise `Bin-laws` from Induction

double : ∀ (n : ℕ) → n + n ≡ 2 * n
double zero = refl
double (suc n) =
  begin
    suc n + suc n           ≡⟨⟩
    suc (n + suc n)         ≡⟨ cong suc (+-suc n n) ⟩
    suc (suc (n + n))       ≡⟨ cong (suc ∘ suc) (double n) ⟩
    suc (suc (2 * n))       ≡⟨⟩
    suc (suc (n + (n + 0))) ≡⟨ cong suc (sym (+-suc n (n + zero))) ⟩
    suc (n + suc (n + 0))   ≡⟨⟩
    2 * suc n
  ∎

inc-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
inc-suc ⟨⟩ = refl
inc-suc (b O) = refl
inc-suc (b I) =
  begin
    from (inc (b I))                  ≡⟨⟩
    from (inc b) + (from (inc b) + 0) ≡⟨ cong (from (inc b) +_) (+-identityʳ (from (inc b))) ⟩
    from (inc b) + from (inc b)       ≡⟨ cong (_+ from (inc b)) (inc-suc b) ⟩
    suc (from b) + from (inc b)       ≡⟨ cong (suc (from b) +_) (inc-suc b) ⟩
    suc (from b) + suc (from b)       ≡⟨ +-suc (suc (from b)) (from b) ⟩
    suc (suc (from b) + from b)       ≡⟨ cong suc (+-comm (suc (from b)) (from b)) ⟩
    suc (from b + suc (from b))       ≡⟨ cong suc (+-suc (from b) (from b)) ⟩
    suc (suc (from b + from b))       ≡⟨ cong (suc ∘ suc) (double (from b)) ⟩
    suc (suc (2 * from b))            ≡⟨⟩
    suc (from (b I))
  ∎

iso-to∘from-cex : to (from ⟨⟩) ≢ ⟨⟩
iso-to∘from-cex = λ ()

iso-from∘to : ∀ (n : ℕ) → from (to n) ≡ n
iso-from∘to zero = refl
iso-from∘to (suc n) =
  begin
    from (to (suc n)) ≡⟨⟩
    from (inc (to n)) ≡⟨ inc-suc (to n) ⟩
    suc (from (to n)) ≡⟨ cong suc (iso-from∘to n) ⟩
    suc n
  ∎

-- Exercise `Bin-predicates` from Relations

-- "Obvious" definition

-- This is a straightforward way to define binary numbers with leading
-- 1 but it makes some of the proofs around canonical representations
-- more complicated than they need to be. For the sake of not being
-- shady, I prove here that the two definitions are equivalent.

data One′ : Bin → Set where
  one′ : One′ (⟨⟩ I)
  zeroFollow : ∀ {b : Bin} → One′ b → One′ (b O)
  oneFollow : ∀ {b : Bin} → One′ b → One′ (b I)

-- "Nice" definition

-- This is mainly just to make the proof of `to∘from-One` much much
-- easier. I banged my head against the version for `One′` for long
-- enough that I was very pleased to find such a compact proof with
-- just a change of definition.

data One : Bin → Set where
  one : One (⟨⟩ I)
  suc : ∀ {b : Bin} → One b → One (inc b)

-- We need some lemmas here to recover the constructors of each
-- definition.

inc-One′ : ∀ (b : Bin) → One′ b → One′ (inc b)
inc-One′ ⟨⟩ ()
inc-One′ (b O) (zeroFollow ob) = oneFollow ob
inc-One′ (.⟨⟩ I) one′ = zeroFollow one′
inc-One′ (b I) (oneFollow ob) = zeroFollow (inc-One′ b ob)

One-zeroFollow : ∀ {b : Bin} → One b → One (b O)
One-zeroFollow one = suc one
One-zeroFollow (suc b) = suc (suc (One-zeroFollow b))

One-oneFollow : ∀ {b : Bin} → One b → One (b I)
One-oneFollow one = suc (suc one)
One-oneFollow (suc b) = suc (suc (One-oneFollow b))

-- And at last we can show that the two definitions are equivalent.

One≡One′ : ∀ {b : Bin} → One b → One′ b
One≡One′ one = one′
One≡One′ (suc one) = zeroFollow one′
One≡One′ (suc (suc b)) with One≡One′ b
...                    | one′ = oneFollow one′
...                    | zeroFollow {b′} w = zeroFollow (inc-One′ b′ w)
...                    | oneFollow {b′} w = oneFollow (inc-One′ b′ w)

One′≡One : ∀ {b : Bin} → One′ b → One b
One′≡One one′ = one
One′≡One (zeroFollow b) with One′≡One b
...                     | one = suc one
...                     | suc w = suc (suc (One-zeroFollow w))
One′≡One (oneFollow b) with One′≡One b
...                    | one = suc (suc one)
...                    | suc w = One-oneFollow (suc w)

data Can : Bin → Set where
  zero : Can (⟨⟩ O)
  oneLead : ∀ {b : Bin} → One b → Can b

inc-Can : ∀ {b : Bin} → Can b → Can (inc b)
inc-Can zero = oneLead one
inc-Can (oneLead one) = oneLead (suc one)
inc-Can (oneLead (suc b)) = oneLead (suc (suc b))

to-Can : ∀ (n : ℕ) → Can (to n)
to-Can zero = zero
to-Can (suc n) = inc-Can (to-Can n)

to∘from-One : ∀ {b : Bin} → One b → to (from b) ≡ b
to∘from-One one = refl
to∘from-One (suc {b} b′) =
  begin
    to (from (inc b)) ≡⟨ cong to (inc-suc b) ⟩
    to (suc (from b)) ≡⟨⟩
    inc (to (from b)) ≡⟨ cong inc (to∘from-One b′) ⟩
    inc b
  ∎

to∘from-Can : ∀ {b : Bin} → Can b → to (from b) ≡ b
to∘from-Can zero = refl
to∘from-Can (oneLead b) = to∘from-One b
