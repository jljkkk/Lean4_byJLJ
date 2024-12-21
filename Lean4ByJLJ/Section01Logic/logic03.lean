import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h1
  apply h1
  trivial
  done

example : False → ¬True := by
  intro h1
  intro h2
  exact h1
  done

example : ¬False → True := by
  intro h1
  trivial
  done

example : True → ¬False := by
  intro h1
  intro h2
  exact h2
  done

example : False → ¬P := by
  intro h1
  intro h2
  exact h1
  done

example : P → ¬P → False := by
  intro h1
  intro h2
  apply h2 at h1
  exact h1
  done

example : P → ¬¬P := by
  intro h1
  intro h2
  apply h2 at h1
  exact h1
  done

example : (P → Q) → ¬Q → ¬P := by
  intro h1
  intro h2
  intro h3
  apply h1 at h3
  apply h2 at h3
  exact h3
  done

example : ¬¬False → False := by
  intro h1
  apply h1
  intro h2
  exact h2
  done

example : ¬¬P → P := by
  intro h1
  by_contra h2
  apply h1 at h2
  exact h2
  done

example : (¬Q → ¬P) → P → Q := by
  intro h1
  intro h2
  by_contra h3
  apply h1 at h3
  apply h3 at h2
  exact h2
  done
