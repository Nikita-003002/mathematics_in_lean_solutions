import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    apply h
    use x
  · intro h x x''s
    rcases x''s with ⟨x', xs, e⟩
    rw [← e]
    apply h
    exact xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x xs
  rcases xs with ⟨x', x's, e⟩
  have h': x' = x := by
    apply h
    exact e
  rw[← h']
  exact x's

example : f '' (f ⁻¹' u) ⊆ u := by
  intro x h
  rcases h with ⟨y, hy, yx⟩
  rw[← yx]
  apply hy

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x hx
  obtain ⟨y, hy⟩ := h x
  use y
  constructor
  · apply hy.symm ▸ hx
  exact hy

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x hx
  rcases hx with ⟨y, ys, fyx⟩
  use y
  constructor
  apply h
  exact ys
  exact fyx

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x hu
  apply h
  exact hu

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  · intro h
    exact h
  · intro h
    exact h

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x h
  rcases h with ⟨y, ⟨ys, yt⟩, fyx⟩
  constructor
  · exact ⟨y, ys, fyx⟩
  · exact ⟨y, yt, fyx⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x ⟨hxs, hxt⟩
  rcases hxs with ⟨a, ha, fax⟩
  rcases hxt with ⟨b, hb, fbx⟩
  have hab: b = a := by apply h; rw[fax, fbx]
  subst hab
  use b
  constructor
  · exact ⟨ha, hb⟩
  · exact fax

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x h
  obtain ⟨x_in_s, x_not_in_t⟩ := h
  rcases x_in_s with ⟨a, has, rfl⟩
  use a
  constructor
  · constructor
    .exact has
    · intro h'
      apply x_not_in_t
      use a
  · rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x h
  obtain ⟨hu, hv⟩ := h
  constructor
  · exact hu
  · exact hv

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  constructor
  · intro h
    rcases h with ⟨hs, xv⟩
    rcases hs with ⟨y, ys, fyx⟩
    use y
    constructor
    · constructor
      exact ys
      · apply fyx.symm ▸ xv
    exact fyx
  · intro h
    rcases h with ⟨y, ⟨ ⟨ys, yfv⟩, fyx⟩⟩
    constructor
    use y
    have h': x = f y := by rw[fyx]
    rw[h']
    exact yfv

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro x h
  rcases h with ⟨y, ⟨fy, yfu⟩, fyx⟩
  constructor
  · use y
  rw[← fyx]
  exact yfu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x h
  rcases h with ⟨xs, xfu⟩
  constructor
  · use x
  exact xfu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x h
  rcases h with (xs | xfu)
  constructor
  · use x
  · right
    exact xfu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  constructor
  simp only [Set.mem_image, Set.mem_iUnion]
  · rintro ⟨y, ⟨i, hi⟩, fyx⟩
    use i, y
  · rintro ⟨sb, sb_range, xsb⟩
    · rcases sb_range with ⟨i, rfl⟩
      rcases xsb with ⟨a, ha, rfl⟩
      use a
      constructor
      simp only [Set.mem_iUnion]
      use i, ha
      · rfl

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  sorry

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  sorry

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos e
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  sorry

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

-- COMMENTS: TODO: improve this
end
