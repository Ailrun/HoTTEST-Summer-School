# Week 9 - Cubical Agda Exercises

## Standard disclaimer:

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

In case you haven't done the other Agda exercises:
This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**When solving the problems,
please make a copy of this file to work in, so that it doesn't get overwritten
(in case we update the exercises through `git`)!**


```agda
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Exercises9 where

open import cubical-prelude
open import Lecture7-notes
open import Lecture8-notes
open import Lecture9-notes
open import Solutions7 hiding (rUnit)
open import Solutions8
open import Lecture9-live using (SemiGroupℕ)
```

## Part I: More hcomps

### Exercise 1 (★★)
### (a)
Show the left cancellation law for path composition using an hcomp.
Hint: one hcomp should suffice. Use `comp-filler` and connections

```agda
lUnit : {A : Type ℓ} {x y : A} (p : x ≡ y) → refl ∙ p ≡ p
lUnit {x = x} p i j =
  hcomp
    (λ { k (i = i0) → comp-filler refl p k j
       ; k (i = i1) → p (j ∧ k)
       ; k (j = i0) → x
       ; k (j = i1) → p k })
    x
```

### (b)
Try to mimic the construction of lUnit for rUnit (i.e. redefine it)
in such a way that `rUnit refl ≡ lUnit refl` holds by `refl`.
Hint: use (almost) the exact same hcomp.

```agda
rUnit : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
rUnit {x = x} {y = y} p i j =
  hcomp
    (λ { k (i = i0) → comp-filler p refl k j
       ; k (i = i1) → p j
       ; k (j = i0) → x
       ; k (j = i1) → y })
    (p j)

-- uncomment to see if it type-checks

rUnit≡lUnit : ∀ {ℓ} {A : Type ℓ} {x : A} → rUnit (refl {x = x}) ≡ lUnit refl
rUnit≡lUnit = refl
```


### Exercise 2 (★★)
Show the associativity law for path composition
Hint: one hcomp should suffice. This one can be done without connections
  (but you might need comp-filler in more than one place)

```agda
assoc : {A : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
assoc {x = x} p q r i j =
  hcomp
    (λ{ k (i = i0) → (p ∙ comp-filler q r k) j
      ; k (i = i1) → comp-filler (p ∙ q) r k j
      ; k (j = i0) → x
      ; k (j = i1) → r k })
    ((p ∙ q) j)
```

### Exercise 3 (Master class in connections) (🌶)
The goal of this exercise is to give a cubical proof of the Eckmann-Hilton argument,
which says that path composition for higher loops is commutative

(a) While we cannot get `p ∙ q ≡ q ∙ p` as a one-liner, we can get a
one-liner showing that the identiy holds up to some annoying
coherences.  Try to understand the following statement (and why it's
well-typed). After that, fill the holes

Hint: each hole will need a `∨` or a `∧`

```agda
pre-EH : {A : Type ℓ} {x : A} (p q : refl {x = x} ≡ refl)
  → ap (λ x → x ∙ refl) p ∙ ap (λ x → refl ∙ x) q -- [ refl ∙ refl ≡ refl ∙ refl ]
   ≡ ap (λ x → refl ∙ x) q ∙ ap (λ x → x ∙ refl) p
pre-EH {x = x} p q i = (λ j → p (~ i ∧ j) ∙ q (i ∧ j))
                     ∙ (λ j → p (~ i ∨ j) ∙ q (i ∨ j))
```
(b) If we manage to cancel out all of the annoying aps, we get Eckmann-Hilton:
For paths (p q : refl ≡ refl), we have p ∙ q ≡ q ∙ p. Try to prove this, using the above lemma.

Hint: Use the pre-EH as the bottom of an hcomp (one should be enough).
For the sides, use lUnit and rUnit wherever they're needed. Note that this will only work out smoothly if
you've solved Exercise 1 (b).

```agda
Eckmann-Hilton : {A : Type ℓ} {x : A} (p q : refl {x = x} ≡ refl) → p ∙ q ≡ q ∙ p
Eckmann-Hilton p q i j =
  hcomp
    (λ{ k (i = i0)  → ((λ j → rUnit (p j) k) ∙ (λ j → lUnit (q j) k)) j
      ; k (i = i1)  → ((λ j → lUnit (q j) k) ∙ (λ j → rUnit (p j) k)) j
      ; k (j = i0)  → rUnit refl k
      ; k (j = i1)  → rUnit refl k })
    (pre-EH p q i j)
```
# Part 2: Binary numbers as a HIT
Here is another HIT describing binary numbers. The idea is that a binary number is a list of booleans, modulo trailing zeros.

For instance, `true ∷ true ∷ true ∷ []` is the binary number 110 ...
... and so is `true ∷ true ∷ false ∷ false ∷ false ∷ []`

(!) Note that we're interpreting 110 as 1·2⁰ + 1·2¹ + 0·2² here.

```agda
0B = false
1B = true

data ListBin : Type where
  []    : ListBin
  _∷_   : (x : Bool) (xs : ListBin) → ListBin
  drop0 : 0B ∷ [] ≡ []

-- 1 as a binary number
1LB : ListBin
1LB = 1B ∷ []
```
### Exercise 4 (★)
Define the successor function on ListBin
```agda
sucListBin : ListBin → ListBin
sucListBin [] = 1LB
sucListBin (true ∷ xs) = false ∷ sucListBin xs
sucListBin (false ∷ xs) = true ∷ xs
sucListBin (drop0 i) = 1LB
```
### Exercise 5 (★★)
Define an addition `+LB` on ListBin and prove that `x +LB [] ≡ x`
Do this by mutual induction! Make sure the three cases for the right unit law hold by refl.
```agda
_+LB_ : ListBin → ListBin → ListBin
rUnit+LB : (x : ListBin) → x +LB [] ≡ x

[] +LB y = y
(b ∷ x) +LB [] = b ∷ x
(true ∷ x) +LB (true ∷ y) = 0B ∷ sucListBin (x +LB y)
(true ∷ x) +LB (false ∷ y) = 1B ∷ (x +LB y)
(false ∷ x) +LB (c ∷ y) = c ∷ (x +LB y)
(true ∷ x) +LB drop0 i = 1B ∷ rUnit+LB x i
(false ∷ x) +LB drop0 i = 0B ∷ rUnit+LB x i
drop0 i +LB [] = drop0 i
drop0 i +LB (x ∷ y) = x ∷ y
drop0 i +LB drop0 j = drop0 (i ∧ j)

rUnit+LB [] = refl
rUnit+LB (b ∷ xs) = refl
rUnit+LB (drop0 i) = refl

```
(c) Prove that sucListBin is left distributive over `+LB`
Hint: If you pattern match deep enough, there should be a lot of refls...
```agda
sucListBinDistrL : (x y : ListBin) → sucListBin (x +LB y) ≡ (sucListBin x +LB y)
sucListBinDistrL [] [] = refl
sucListBinDistrL [] (true ∷ y) = refl
sucListBinDistrL [] (false ∷ y) = refl
sucListBinDistrL [] (drop0 j) = refl
sucListBinDistrL (true ∷ x) [] = refl
sucListBinDistrL (false ∷ x) [] = refl
sucListBinDistrL (true ∷ x) (true ∷ y) = ap (1B ∷_) (sucListBinDistrL x y)
sucListBinDistrL (true ∷ x) (false ∷ y) = ap (0B ∷_) (sucListBinDistrL x y)
sucListBinDistrL (false ∷ x) (true ∷ y) = refl
sucListBinDistrL (false ∷ x) (false ∷ y) = refl
sucListBinDistrL (true ∷ []) (drop0 j) = refl
sucListBinDistrL (true ∷ (true ∷ x)) (drop0 j) = refl
sucListBinDistrL (true ∷ (false ∷ x)) (drop0 j) = refl
sucListBinDistrL (true ∷ drop0 i) (drop0 j) = refl
sucListBinDistrL (false ∷ x) (drop0 j) = refl
sucListBinDistrL (drop0 i) [] = refl
sucListBinDistrL (drop0 i) (true ∷ y) = refl
sucListBinDistrL (drop0 i) (false ∷ y) = refl
sucListBinDistrL (drop0 i) (drop0 j) = refl
```

### Exercise 6 (★)
Define a map `LB→ℕ : ListBin → ℕ` and show that it preserves addition

```agda
ℕ→ListBin : ℕ → ListBin
ℕ→ListBin zero = []
ℕ→ListBin (suc x) = sucListBin (ℕ→ListBin x)

ℕ→ListBin-pres+ : (x y : ℕ) → ℕ→ListBin (x + y) ≡ (ℕ→ListBin x +LB ℕ→ListBin y)
ℕ→ListBin-pres+ zero y = refl
ℕ→ListBin-pres+ (suc x) y = ap sucListBin (ℕ→ListBin-pres+ x y) ∙ sucListBinDistrL (ℕ→ListBin x) (ℕ→ListBin y)
```

### Exercise 7 (★★★)
Show that `ℕ ≃ ListBin`.

```agda
ListBin→ℕ : ListBin → ℕ
ListBin→ℕ [] = 0
ListBin→ℕ (true ∷ x) = suc (ListBin→ℕ x + ListBin→ℕ x)
ListBin→ℕ (false ∷ x) = ListBin→ℕ x + ListBin→ℕ x
ListBin→ℕ (drop0 i) = 0

x+LBx : (x : ListBin) → x +LB x ≡ 0B ∷ x
x+LBx [] i = drop0 (~ i)
x+LBx (true ∷ x) = ap (0B ∷_) (ap sucListBin (x+LBx x))
x+LBx (false ∷ x) = ap (0B ∷_) (x+LBx x)
x+LBx (drop0 i) j =
  hcomp
    (λ { k (i = i0) → 0B ∷ drop0 (~ j ∨ ~ k)
       ; k (i = i1) → drop0 (~ j)
       ; k (j = i0) → drop0 i
       ; k (j = i1) → 0B ∷ drop0 (i ∨ ~ k) })
    (drop0 (i ∧ ~ j))

ListBin→ℕ→ListBin : (x : ListBin) → ℕ→ListBin (ListBin→ℕ x) ≡ x
ListBin→ℕ→ListBin [] = refl
ListBin→ℕ→ListBin (true ∷ x) =
  ap
    sucListBin
    ( ℕ→ListBin (ListBin→ℕ x + ListBin→ℕ x) ≡⟨ ℕ→ListBin-pres+ (ListBin→ℕ x) _ ⟩
      ℕ→ListBin (ListBin→ℕ x) +LB ℕ→ListBin (ListBin→ℕ x) ≡⟨ ap (λ x → x +LB x) (ListBin→ℕ→ListBin x) ⟩
      x +LB x ≡⟨ x+LBx _ ⟩
      0B ∷ x ∎)
ListBin→ℕ→ListBin (false ∷ x) =
  ℕ→ListBin (ListBin→ℕ x + ListBin→ℕ x) ≡⟨ ℕ→ListBin-pres+ (ListBin→ℕ x) _ ⟩
  ℕ→ListBin (ListBin→ℕ x) +LB ℕ→ListBin (ListBin→ℕ x) ≡⟨ ap (λ x → x +LB x) (ListBin→ℕ→ListBin x) ⟩
  x +LB x ≡⟨ x+LBx _ ⟩
  0B ∷ x ∎
ListBin→ℕ→ListBin (drop0 i) = lemma i
  where
    lemma : PathP (λ i → [] ≡ drop0 i) (refl ∙ refl ∙ sym drop0 ∙ refl) refl
    lemma i j =
      hcomp
        (λ { k (i = i0) → (lUnit (refl ∙ sym drop0 ∙ refl) ∙ lUnit (sym drop0 ∙ refl) ∙ rUnit (sym drop0)) (~ k) j
           ; k (i = i1) → []
           ; k (j = i0) → []
           ; k (j = i1) → drop0 i })
        (drop0 (i ∨ ~ j))

n+suc[m]≡suc[n+m] : (n m : ℕ) → n + suc m ≡ suc (n + m)
n+suc[m]≡suc[n+m] zero m = refl
n+suc[m]≡suc[n+m] (suc n) m = ap suc (n+suc[m]≡suc[n+m] n m)

ListBin→ℕ-sucListBin : (x : ListBin) → ListBin→ℕ (sucListBin x) ≡ suc (ListBin→ℕ x)
ListBin→ℕ-sucListBin [] = refl
ListBin→ℕ-sucListBin (true ∷ x) =
  ListBin→ℕ (sucListBin x) + ListBin→ℕ (sucListBin x) ≡⟨ ap (λ x → x + x) (ListBin→ℕ-sucListBin x) ⟩
  suc (ListBin→ℕ x) + suc (ListBin→ℕ x) ≡⟨ n+suc[m]≡suc[n+m] (suc (ListBin→ℕ x)) _ ⟩
  suc (suc (ListBin→ℕ x + ListBin→ℕ x)) ∎
ListBin→ℕ-sucListBin (false ∷ x) = refl
ListBin→ℕ-sucListBin (drop0 i) = refl

ℕ→ListBin→ℕ : (x : ℕ) → ListBin→ℕ (ℕ→ListBin x) ≡ x
ℕ→ListBin→ℕ zero = refl
ℕ→ListBin→ℕ (suc x) = ListBin→ℕ-sucListBin (ℕ→ListBin x) ∙ ap suc (ℕ→ListBin→ℕ x)

ℕ≃ListBin : ℕ ≃ ListBin
ℕ≃ListBin = isoToEquiv (iso ℕ→ListBin ListBin→ℕ ListBin→ℕ→ListBin ℕ→ListBin→ℕ)
```
# Part 3: The SIP
### Exericise 8 (★★)
Show that, using an SIP inspired argument, if `(A , _+A_)` is a semigroup and `(B , _+B_)` is some other type with a composition satisfying:

(i) `e : A ≃ B`

(ii) `((x y : A) → e (x +A y) ≡ e x +B e y`

then `(B , _+B_)` defines a semigroup.

Conclude that `(ListBin , _+LB_)` is a semigroup

For inspiration, see Lecture9-notes
```agda

Semigroup≃ : {A B : Type} (SemiGroupA : SemiGroup A) (_+B_ : B → B → B) (e : A ≃ B) →
             ((x y : A) → e .pr₁ (SemiGroupA .pr₁ x y) ≡ e .pr₁ x +B e .pr₁ y) →
             SemiGroup B
Semigroup≃ {A} {B} SemiGroupA _+B_ e h = SemiGroupB
  where
    _+A_ = SemiGroupA .pr₁

    SemiGroupBSIP : SemiGroup B
    SemiGroupBSIP = substEquiv SemiGroup e SemiGroupA

    _+BSIP_ : B → B → B
    _+BSIP_ = SemiGroupBSIP .pr₁

    +BSIP≡+B : _+BSIP_ ≡ _+B_
    +BSIP≡+B i x y = lemma i
      where
        lemma : x +BSIP y ≡ x +B y
        lemma =
          x +BSIP y ≡⟨ transportRefl _ ⟩
          e .pr₁ (invEq e (transport refl x) +A invEq e (transport refl y)) ≡⟨ (λ i → e .pr₁ (invEq e (transportRefl x i) +A invEq e (transportRefl y i))) ⟩
          e .pr₁ (invEq e x +A invEq e y) ≡⟨ h (invEq e x) (invEq e y) ⟩
          e .pr₁ (invEq e x) +B e .pr₁ (invEq e y) ≡⟨ (λ i → secEq e x i +B secEq e y i) ⟩
          x +B y ∎

    SemiGroupB : SemiGroup B
    SemiGroupB = _+B_ , subst (λ _op_ → (x y z : B) → x op (y op z) ≡ (x op y) op z) +BSIP≡+B (SemiGroupBSIP .pr₂)

SemiGroupListBin : SemiGroup ListBin
SemiGroupListBin = Semigroup≃ (_+_ , +-assoc) _+LB_ ℕ≃ListBin ℕ→ListBin-pres+
