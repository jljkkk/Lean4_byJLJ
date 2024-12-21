import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro h1
  left
  exact h1
  done

example : Q → P ∨ Q := by
  intro h1
  right
  exact h1
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h1
  intro h2
  intro h3
  cases' h1 with h11 h12
  apply h2 at h11
  exact h11
  apply h3 at h12
  exact h12
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h1
  cases' h1 with h11 h12
  right
  exact h11
  left
  exact h12
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
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
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1
  intro h2
  intro h3
  cases' h3 with h31 h32
  apply h1 at h31
  left
  exact h31
  apply h2 at h32
  right
  exact h32
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h1
  intro h2
  cases' h2 with h21 h22
  apply h1 at h21
  left
  exact h21
  right
  exact h22
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1
  intro h2
  constructor
  rw[h2]
  rw[h1]
  intro h2
  exact h2
  rw[h2]
  rw[h1]
  intro h2
  exact h2
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro h1
  constructor
  intro h2
  apply h1
  left
  exact h2
  intro h2
  apply h1
  right
  exact h2
  intro h1
  intro h2
  cases' h1 with h11 h12
  cases' h2 with h21 h22
  apply h11 at h21
  exact h21
  apply h12 at h22
  exact h22
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  intro h1
  by_cases h2:P
  right
  intro h3
  apply h1
  constructor
  exact h2
  exact h3
  left
  exact h2
  intro h1
  intro h2
  cases' h1 with h11 h12
  apply h11
  cases' h2 with h21 h22
  exact h21
  apply h12
  cases' h2 with h21 h22
  exact h22
  done
