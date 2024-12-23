import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 6 : pushforward and pullback

## Pushforward of a set along a map

If `f : X → Y` then given a subset `S : Set X` of `X` we can push it
forward along `f` to make a subset `f(S) : Set Y` of `Y`. The definition
of `f(S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`.

However `f(S)` doesn't make sense in Lean, because `f` eats
terms of type `X` and not `S`, which has type `Set X`.
In Lean we use the notation `f '' S` for this. This is notation
for `Set.image` and if you need any API for this, it's likely
to use the word `image`.

## Pullback of a set along a map

If `f : X → Y` then given a subset `T : Set Y` of `Y` we can
pull it back along `f` to make a subset `f⁻¹(T) : Set X` of `X`. The
definition of `f⁻¹(T)` is `{x : X | f x ∈ T}`.

However `f⁻¹(T)` doesn't make sense in Lean either, because
`⁻¹` is notation for `Inv.inv`, whose type in Lean
is `α → α`. In other words, if `x` has a certain type, then
`x⁻¹` *must* have the same type: the notation was basically designed
for group theory. In Lean we use the notation `f ⁻¹' T` for this pullback.

-/

variable (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y)

example : S ⊆ f ⁻¹' (f '' S) := by
  intro x h
  simp
  use x


example : f '' (f ⁻¹' T) ⊆ T := by
  intro x h
  simp at h
  cases' h with y h1
  cases' h1 with hy hxy
  rw [← hxy]
  exact hy


-- `library_search` will do this but see if you can do it yourself.
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  constructor
  intro h1 x h2
  simp
  apply h1
  use x
  intro h1 x h2
  simp at h2
  cases' h2 with y h3
  cases' h3 with hy hxy
  rw [← hxy]
  apply h1 at hy
  simp at hy
  exact hy




-- Pushforward and pullback along the identity map don't change anything
-- pullback is not so hard
example : id ⁻¹' S = S := by
  ext x
  constructor
  intro h1
  simp at h1
  exact h1
  intro h1
  simp
  exact h1

-- pushforward is a little trickier. You might have to `ext x, split`.
example : id '' S = S := by
  ext x
  constructor
  intro h1
  simp at h1
  exact h1
  intro h1
  simp
  exact h1

-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- preimage of preimage is preimage of comp
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  ext x
  constructor
  intro h1
  simp
  simp at h1
  exact h1
  intro h1
  simp
  simp at h1
  exact h1

-- preimage of preimage is preimage of comp
example : g ∘ f '' S = g '' (f '' S) := by
  ext x
  constructor
  intro h1
  simp
  simp at h1
  exact h1
  intro h1
  simp
  simp at h1
  exact h1
