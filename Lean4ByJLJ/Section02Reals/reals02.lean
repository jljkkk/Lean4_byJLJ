import Mathlib.Tactic -- import all the tactics

/-!

# Doing algebra in the real numbers

The `ring` tactic will prove algebraic identities like
(x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 in rings, and Lean
knows that the real numbers are a ring. See if you can use
`ring` to prove these theorems.

## New tactics you will need

* `ring`
* `intro` (new functionality: use on a goal of type `⊢ ∀ x, ...`)

-/

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring
  done

example : ∀ a b : ℝ, ∃ x, (a + b) ^ 3 = a ^ 3 + x * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  intro a
  intro b
  use 3
  ring
  done

example : ∃ x : ℝ, ∀ y, y + y = x * y := by
  use 2
  intro y
  ring
  done

example : ∀ x : ℝ, ∃ y, x + y = 2 := by
  intro x
  use 2-x
  ring
  done

example : ∀ x : ℝ, ∃ y, x + y ≠ 2 := by
  intro x
  use 3-x
  ring
  norm_num
  done