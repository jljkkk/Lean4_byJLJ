import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext x
  constructor
  intro h1
  cases' h1 with h11 h12
  exact h11
  exact h12
  intro h1
  right
  exact h1

example : A ∩ A = A := by
  ext x
  constructor
  intro h1
  cases' h1 with h11 h12
  exact h11
  intro h1
  constructor
  exact h1
  exact h1

example : A ∩ ∅ = ∅ := by
  ext x
  constructor
  intro h1
  cases' h1 with h11 h12
  exact h12
  intro h1
  constructor
  by_contra h2
  apply h1
  exact h1


example : A ∪ univ = univ := by
  ext x
  constructor
  intro h1
  trivial
  intro h1
  right
  exact h1

example : A ⊆ B → B ⊆ A → A = B := by
  intro h1 h2
  ext x
  constructor
  intro h3
  apply h1 at h3
  exact h3
  intro h3
  apply h2 at h3
  exact h3

example : A ∩ B = B ∩ A := by
  ext x
  constructor
  intro h1
  cases' h1 with h11 h12
  constructor
  exact h12
  exact h11
  intro h1
  cases' h1 with h11 h12
  constructor
  exact h12
  exact h11

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext x
  constructor
  intro h1
  cases' h1 with h11 h12
  cases' h12 with h121 h122
  constructor
  constructor
  exact h11
  exact h121
  exact h122
  intro h1
  cases' h1 with h11 h12
  cases' h11 with h111 h112
  constructor
  exact h111
  constructor
  exact h112
  exact h12

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext x
  constructor
  intro h1
  cases' h1 with h11 h12
  left
  left
  exact h11
  cases' h12 with h121 h122
  left
  right
  exact h121
  right
  exact h122
  intro h1
  cases' h1 with h11 h12
  cases' h11 with h111 h112
  left
  exact h111
  right
  left
  exact h112
  right
  right
  exact h12

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  intro h1
  cases' h1 with h11 h12
  constructor
  left
  exact h11
  left
  exact h11
  cases' h12 with h121 h122
  constructor
  right
  exact h121
  right
  exact h122
  intro h1
  cases' h1 with h11 h12
  cases' h11 with h111 h112
  left
  exact h111
  cases' h12 with h121 h122
  left
  exact h121
  right
  constructor
  exact h112
  exact h122


example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext x
  constructor
  intro h1
  cases' h1 with h11 h12
  cases' h12 with h121 h122
  left
  constructor
  exact h11
  exact h121
  right
  constructor
  exact h11
  exact h122

  intro h1
  constructor
  cases' h1 with h11 h12
  cases' h11 with h111 h112
  exact h111
  cases' h12 with h121 h122
  exact h121
  cases' h1 with h11 h12
  cases' h11 with h111 h112
  left
  exact h112
  right
  cases' h12 with h121 h122
  exact h122
