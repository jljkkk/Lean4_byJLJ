import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro h1
  cases' h1 with h11 h12
  exact h11
  done

example : P ∧ Q → Q := by
  intro h1
  cases' h1 with h11 h12
  exact h12
  done

example : (P → Q → R) → P ∧ Q → R := by
  intro h1
  intro h2
  cases' h2 with h21 h22
  apply h1 at h21
  apply h21 at h22
  exact h22
  done

example : P → Q → P ∧ Q := by
  intro h1
  intro h2
  constructor
  exact h1
  exact h2
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro h1
  cases' h1 with h11 h12
  constructor
  exact h12
  exact h11
  done

example : P → P ∧ True := by
  intro h1
  constructor
  exact h1
  trivial
  done

example : False → P ∧ False := by
  intro h1
  constructor
  exfalso
  exact h1
  exact h1
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1
  intro h2
  cases' h1 with h11 h12
  cases' h2 with h21 h22
  constructor
  exact h11
  exact h22
  done

example : (P ∧ Q → R) → P → Q → R := by
  intro h1
  intro h2
  intro h3
  apply h1
  constructor
  exact h2
  exact h3
  done
