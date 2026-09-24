import ShapleyValue.Uniqueness

namespace ShapleyValue.Palomar

variable (N : Type*) [Fintype N] [DecidableEq N]

theorem shapley_characterization (ψ : Game N → N → ℝ) :
    (Efficient N ψ ∧ Symmetric N ψ ∧ NullPlayer N ψ ∧ Additive N ψ) ↔
      ψ = shapleyValue N :=
  ShapleyValue.shapley_characterization N ψ

theorem shapleyValue_unique (ψ : Game N → N → ℝ) (hE : Efficient N ψ)
    (hS : Symmetric N ψ) (hN : NullPlayer N ψ) (hA : Additive N ψ) :
    ψ = shapleyValue N :=
  ShapleyValue.shapleyValue_unique N ψ hE hS hN hA

theorem shapleyValue_efficient : Efficient N (shapleyValue N) :=
  ShapleyValue.shapleyValue_efficient N

theorem shapleyValue_symmetric : Symmetric N (shapleyValue N) :=
  ShapleyValue.shapleyValue_symmetric N

theorem shapleyValue_nullPlayer : NullPlayer N (shapleyValue N) :=
  ShapleyValue.shapleyValue_nullPlayer N

theorem shapleyValue_additive : Additive N (shapleyValue N) :=
  ShapleyValue.shapleyValue_additive N

end ShapleyValue.Palomar
