import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → False` are all equal *by definition*
in Lean.

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`.

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `False`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why, it's a good logic exercise.

-/


open Set

variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : x ∉ A → x ∈ A → False := by
  intro h1 h2
  apply h1
  exact h2

example : x ∈ A → x ∉ A → False := by
  intro h1 h2
  apply h2
  exact h1

example : A ⊆ B → x ∉ B → x ∉ A := by
  intro h1 h2 h3
  apply h2
  apply h1 at h3
  exact h3


-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : Set X) := by
  intro h1
  cases h1

example : x ∈ Aᶜ → x ∉ A := by
  intro h1
  exact h1

example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  constructor
  intro h1 h2
  cases' h2 with x h3
  specialize h1 x
  apply h3
  exact h1
  intro h1 x
  by_contra h2
  apply h1
  use x
  intro h1
  apply h2 at h1
  exact h1


example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by
  constructor
  intro h1 h2
  cases' h1 with x h3
  specialize h2 x
  apply h2 at h3
  exact h3
  intro h1
  by_contra h2
  apply h1
  intro x h3
  apply h2
  use x
