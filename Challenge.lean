import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace ShapleyValue

variable (N : Type*) [Fintype N] [DecidableEq N]

open scoped Nat BigOperators

/-- A cooperative (TU) game is a characteristic function `v : Finset N → ℝ`
normalized by `v ∅ = 0`. -/
def Game (N : Type*) : Type _ := { f : Finset N → ℝ // f ∅ = 0 }

namespace Game

/-- Coercion of a game to its characteristic function. -/
instance : FunLike (Game N) (Finset N) ℝ where
  coe := fun g => g.val
  coe_injective := by
    intro f g h
    apply Subtype.ext
    exact h

/-- The zero cooperative game. -/
instance : Zero (Game N) := ⟨0, by simp⟩

/-- Pointwise addition of cooperative games. -/
instance : Add (Game N) :=
  ⟨fun v w => ⟨v.val + w.val, by simp [v.property, w.property]⟩⟩

/-- Scalar multiplication of a cooperative game. -/
instance : SMul ℝ (Game N) :=
  ⟨fun c v => ⟨c • v.val, by simp [v.property]⟩⟩

omit [Fintype N] [DecidableEq N] in
/-- Evaluation of the sum of two games. -/
@[simp] theorem coe_add (v w : Game N) (S : Finset N) :
    ⇑(v + w) S = ⇑v S + ⇑w S := rfl

omit [Fintype N] [DecidableEq N] in
/-- Evaluation of a scalar multiple of a game. -/
@[simp] theorem coe_smul (c : ℝ) (v : Game N) (S : Finset N) :
    ⇑(c • v) S = c * ⇑v S := rfl

omit [Fintype N] [DecidableEq N] in
/-- Evaluation of the zero game. -/
@[simp] theorem coe_zero (S : Finset N) : ⇑(0 : Game N) S = 0 := rfl

end Game

/-- Shapley weight of a coalition of cardinality `k`, i.e.
`(k-1)! (n-k)! / n!` where `n = Fintype.card N`. -/
noncomputable def weight (k : ℕ) : ℝ :=
  (((k - 1)! * (Fintype.card N - k)! : ℝ) / ((Fintype.card N)! : ℝ))

/-- The Shapley value,
`φᵢ(v) = ∑_{S ∋ i} ((|S|-1)! (n-|S|)! / n!) * (v S - v (S ∖ {i}))`
(Shapley 1953). -/
noncomputable def shapleyValue (v : Game N) (i : N) : ℝ :=
  ∑ S ∈ Finset.univ.powerset.filter (fun S => i ∈ S),
    weight N S.card * (⇑v S - ⇑v (S.erase i))

/-- An allocation rule is efficient if it distributes the worth of the grand coalition. -/
def Efficient (ψ : Game N → N → ℝ) : Prop :=
  ∀ v : Game N, ∑ i, ψ v i = ⇑v Finset.univ

/-- An allocation rule is symmetric if interchangeable players receive equal payoffs. -/
def Symmetric (ψ : Game N → N → ℝ) : Prop :=
  ∀ (v : Game N) (i j : N),
    (∀ S : Finset N, i ∉ S → j ∉ S → ⇑v (insert i S) = ⇑v (insert j S)) →
      ψ v i = ψ v j

/-- An allocation rule satisfies the null-player axiom if null players receive zero. -/
def NullPlayer (ψ : Game N → N → ℝ) : Prop :=
  ∀ (v : Game N) (i : N),
    (∀ S : Finset N, i ∉ S → ⇑v (insert i S) = ⇑v S) → ψ v i = 0

/-- An allocation rule is additive if its value respects addition of games. -/
def Additive (ψ : Game N → N → ℝ) : Prop :=
  ∀ (v w : Game N) (i : N), ψ (v + w) i = ψ v i + ψ w i

namespace Palomar

theorem shapley_characterization (ψ : Game N → N → ℝ) :
    (Efficient N ψ ∧ Symmetric N ψ ∧ NullPlayer N ψ ∧ Additive N ψ) ↔
      ψ = shapleyValue N := by
  sorry

theorem shapleyValue_unique (ψ : Game N → N → ℝ) (hE : Efficient N ψ)
    (hS : Symmetric N ψ) (hN : NullPlayer N ψ) (hA : Additive N ψ) :
    ψ = shapleyValue N := by
  sorry

theorem shapleyValue_efficient : Efficient N (shapleyValue N) := by
  sorry

theorem shapleyValue_symmetric : Symmetric N (shapleyValue N) := by
  sorry

theorem shapleyValue_nullPlayer : NullPlayer N (shapleyValue N) := by
  sorry

theorem shapleyValue_additive : Additive N (shapleyValue N) := by
  sorry

end Palomar

end ShapleyValue
