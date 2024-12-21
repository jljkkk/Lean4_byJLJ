import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro h1
  rw[h1]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro h1
  rw[h1]
  intro h2
  rw[h2]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1
  intro h2
  rw[h1]
  exact h2
  done

example : P ∧ Q ↔ Q ∧ P := by
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
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro h1
  cases' h1 with h11 h12 h13
  cases' h11 with h111 h112
  constructor
  exact h111
  constructor
  exact h112
  exact h12
  intro h1
  cases' h1 with h11 h12 h13
  cases' h12 with h121 h122
  constructor
  constructor
  exact h11
  exact h121
  exact h122
  done

/-!
se trata de hacer intro, constructor, demasiado repetitivo
-/

example : P ↔ P ∧ True := by
  constructor
  intro h1
  constructor
  exact h1
  trivial
  intro h1
  cases' h1 with h11 h12
  exact h11
  done

example : False ↔ P ∧ False := by
  constructor
  intro h1
  constructor
  exfalso
  exact h1
  exact h1
  intro h1
  cases' h1 with h11 h12
  exact h12
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1
  intro h2
  constructor
  rw[h2]
  rw[h1]
  intro h3
  exact h3
  rw[h2]
  rw[h1]
  intro h3
  exact h3
  done

example : ¬(P ↔ ¬P) := by
  intro h1
  cases' h1 with h11 h12
  apply h11
  apply h12
  intro h2
  apply h11 at h2
  apply h2
  apply h12 at h2
  exact h2
  apply h12
  intro h2
  apply h11 at h2
  apply h2
  apply h12 at h2
  exact h2
  done
