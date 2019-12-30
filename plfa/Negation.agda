module plfa.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
--open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
--open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; extensionality; _≲_)
open import plfa.Relations using (_<_; z<s; s<s)
open import plfa.Connectives
  using (_⊎_; inj₁; inj₂; _×_; proj₁; proj₂; ⟨_,_⟩; case-⊎; →-distrib-⊎)

-- Definitions

¬_ : Set → Set
¬ A = A → ⊥

infix 3 ¬_

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x = λ{ ¬x → ¬x x }

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ (λ x → k (inj₁ x)))

-- Examples

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

module ⊥-id where
  private
    id : ⊥ → ⊥
    id x = x

    id′ : ⊥ → ⊥
    id′ ()

    id≡id′ : id ≡ id′
    id≡id′ = extensionality (λ())


-- Exercises

-- Exercise `<-irreflexive`

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive (s<s n) = <-irreflexive n

-- Exercise `trichotomy`

data Trichotomous (m n : ℕ) : Set  where

  less :
      (m < n) × ¬ (m ≡ n) × ¬ (n < m)
      -------
    → Trichotomous m n

  same :
      ¬ (m < n) × (m ≡ n) × ¬ (n < m)
      -------
    → Trichotomous m n

  more :
      ¬ (m < n) × ¬ (m ≡ n) × (n < m)
      -------
    → Trichotomous m n

pred-≡ : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
pred-≡ refl = refl

suc-≡ : ∀ {m n : ℕ} → m ≡ n → suc m ≡ suc n
suc-≡ refl = refl

pred-< : ∀ {m n : ℕ} → suc m < suc n → m < n
pred-< (s<s p) = p

<-trichotomy : ∀ (m n : ℕ) → Trichotomous m n
<-trichotomy zero zero = same ⟨ (λ ()) , ⟨ refl , (λ ()) ⟩ ⟩
<-trichotomy zero (suc n) = less ⟨ z<s , ⟨ (λ ()) , (λ ()) ⟩ ⟩
<-trichotomy (suc m) zero = more ⟨ (λ ()) , ⟨ (λ ()) , z<s ⟩ ⟩
<-trichotomy (suc m) (suc n) with <-trichotomy m n
... | less ⟨ m<n , ⟨ ¬m≡n , ¬m>n ⟩ ⟩ = less ⟨ s<s m<n , ⟨ ¬m≡n ∘ pred-≡ , ¬m>n ∘ pred-< ⟩ ⟩
... | same ⟨ ¬m<n , ⟨ m≡n , ¬m>n ⟩ ⟩ = same ⟨ ¬m<n ∘ pred-< , ⟨ suc-≡ m≡n , ¬m>n ∘ pred-< ⟩ ⟩
... | more ⟨ ¬m<n , ⟨ ¬m≡n , m>n ⟩ ⟩ = more ⟨ ¬m<n ∘ pred-< , ⟨ ¬m≡n ∘ pred-≡ , s<s m>n ⟩ ⟩

-- Exercise `⊎-dual-×`

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = →-distrib-⊎

¬⊎-implies-¬× : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
¬⊎-implies-¬× = case-⊎ (λ ¬a → ¬a ∘ proj₁) (λ ¬b → ¬b ∘ proj₂)

{-

We get stuck here because we can't destruct our negation, and we can't
just magic up A and B out of nowhere. This explanation brought to you
by constructivist gang.

¬×-implies-¬⊎ : ∀ {A B : Set} → ¬ (A × B) → (¬ A) ⊎ (¬ B)
¬×-implies-¬⊎ = λ { ¬a×b → inj₁ {!!} }

¬⊎-embeds-¬× : ∀ {A B : Set} → ¬ (A × B) ≲ (¬ A) ⊎ (¬ B)
¬⊎-embeds-¬× =
  record
    { to = ¬×-implies-¬⊎
    ; from = ¬⊎-implies-¬×
    ; from∘to = {!!}
    }
-}

-- Exercise `Classical`

lem : ∀ (A : Set) → Set
lem A = A ⊎ ¬ A

¬¬-elim : ∀ (A : Set) → Set
¬¬-elim A = ¬ ¬ A → A

pierce : ∀ (A B : Set) → Set
pierce A B = ((A → B) → A) → A

→-¬⊎ : ∀ (A B : Set) → Set
→-¬⊎ A B = (A → B) → ¬ A ⊎ B

demorgan : ∀ (A B : Set) → Set
demorgan A B = ¬ (¬ A × ¬ B) → A ⊎ B

-- lem⇔¬¬elim

lem→¬¬elim : ∀ {A : Set} → lem A → ¬¬-elim A
lem→¬¬elim (inj₁ A)  ¬¬A = A
lem→¬¬elim (inj₂ ¬A) ¬¬A = ⊥-elim (¬¬A ¬A)

¬¬elim→lem : (∀ {A : Set} → ¬¬-elim A) → {A : Set} → lem A
¬¬elim→lem dne = dne em-irrefutable

-- lem⇔→¬⊎

lem→¬⊎ : ∀ {A B : Set} → lem A → →-¬⊎ A B
lem→¬⊎ (inj₁ A)  f = inj₂ (f A)
lem→¬⊎ (inj₂ ¬A) f = inj₁ ¬A

swap : ∀ {A B : Set} → A ⊎ B → B ⊎ A
swap (inj₁ x) = inj₂ x
swap (inj₂ x) = inj₁ x

¬⊎→lem : (∀ {A B : Set} → →-¬⊎ A B) → {A : Set} → lem A
¬⊎→lem ¬⊎ = swap (¬⊎ (λ x → x))

-- lem⇔pierce

lem→pierce : ∀ {A B : Set} → lem A → pierce A B
lem→pierce (inj₁ A) k = A
lem→pierce (inj₂ ¬A) k = k (λ A → ⊥-elim (¬A A))

pierce→lem : (∀ {A B : Set} → pierce A B) → ∀ {A : Set} → lem A
pierce→lem p = p λ ¬lem → ⊥-elim (em-irrefutable ¬lem)

-- demorgan→lem and ¬¬elim→demorgan

demorgan→lem : (∀ {A B : Set} → demorgan A B) → ∀ {A : Set} → lem A
demorgan→lem dem = dem λ { ⟨ ¬x , ¬¬x ⟩ → ¬¬x ¬x }

¬¬elim→demorgan : (∀ {A : Set} → ¬¬-elim A) → ∀ {A B : Set} → demorgan A B
¬¬elim→demorgan elim = λ z → elim (λ z₁ → z ⟨ (λ x → z₁ (inj₁ x)) , (λ x → z₁ (inj₂ x)) ⟩)



{-

This oughta do the trick, since we can get to lem from anything and
back to whatever we like (with some slight indirection through ¬¬-elim
for demorgan).

-}

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-Stable : ∀ {A : Set} → Stable (¬ A)
¬-Stable = ¬¬¬-elim

×-Stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-Stable ¬¬A→A ¬¬B→B ¬¬AB = ⟨ ¬¬A→A (λ ¬A → ¬¬AB λ { ⟨ A , _ ⟩ → ¬A A })
                              , ¬¬B→B (λ ¬B → ¬¬AB λ { ⟨ _ , B ⟩ → ¬B B })
                              ⟩
