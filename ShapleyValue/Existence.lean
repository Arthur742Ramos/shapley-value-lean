import ShapleyValue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

namespace ShapleyValue

variable (N : Type*) [Fintype N] [DecidableEq N]

open scoped BigOperators

private abbrev coalitions (N : Type*) [Fintype N] : Finset (Finset N) :=
  Finset.univ.powerset

private lemma sum_over_members (f : Finset N → ℝ) :
    ∑ i ∈ Finset.univ, ∑ S ∈ (coalitions N).filter (fun S => i ∈ S), f S =
      ∑ S ∈ coalitions N, (S.card : ℝ) * f S := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  calc
    ∑ i ∈ Finset.univ, (if i ∈ S then f S else 0) =
        ∑ i ∈ Finset.univ.filter (fun i => i ∈ S), f S := by
      rw [← Finset.sum_filter]
    _ = ∑ i ∈ S, f S := by
      congr 1
      ext i
      simp
    _ = (S.card : ℝ) * f S := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]

private lemma sum_over_nonmembers (f : Finset N → ℝ) :
    ∑ i ∈ Finset.univ, ∑ T ∈ (coalitions N).filter (fun T => i ∉ T), f T =
      ∑ T ∈ coalitions N, ((Fintype.card N - T.card : ℕ) : ℝ) * f T := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  have hTsub : T ⊆ Finset.univ := Finset.mem_powerset.mp hT
  have hcard : (Finset.univ.filter (fun i : N => i ∉ T)).card =
      Fintype.card N - T.card := by
    rw [show Finset.univ.filter (fun i : N => i ∉ T) = Finset.univ \ T by
      ext i
      simp]
    rw [Finset.card_sdiff_of_subset hTsub, Finset.card_univ]
  calc
    ∑ i ∈ Finset.univ, (if i ∉ T then f T else 0) =
        ∑ i ∈ Finset.univ.filter (fun i : N => i ∉ T), f T := by
      rw [← Finset.sum_filter]
    _ = ((Finset.univ.filter (fun i : N => i ∉ T)).card : ℝ) * f T := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    _ = ((Fintype.card N - T.card : ℕ) : ℝ) * f T := by rw [hcard]

private lemma sum_filter_insert (i : N) (f : Finset N → ℝ) :
    ∑ S ∈ (coalitions N).filter (fun S => i ∈ S), f S =
      ∑ R ∈ (coalitions N).filter (fun R => i ∉ R), f (insert i R) := by
  classical
  unfold coalitions
  refine Finset.sum_nbij' (fun S => S.erase i) (fun R => insert i R) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSP, hiS⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, by simp⟩
    exact (Finset.erase_subset _ _).trans (by intro x hx; simp)
  · intro R hR
    rcases Finset.mem_filter.mp hR with ⟨hRP, hiR⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro x hx
      simp
    · simp
  · intro S hS
    exact Finset.insert_erase (Finset.mem_filter.mp hS).2
  · intro R hR
    exact Finset.erase_insert (Finset.mem_filter.mp hR).2
  · intro S hS
    rw [Finset.insert_erase (Finset.mem_filter.mp hS).2]

private lemma sum_filter_insert_of_not (i j : N) (hij : i ≠ j)
    (f : Finset N → ℝ) :
    ∑ S ∈ (coalitions N).filter (fun S => i ∉ S ∧ j ∈ S), f S =
      ∑ R ∈ (coalitions N).filter (fun R => i ∉ R ∧ j ∉ R), f (insert j R) := by
  classical
  unfold coalitions
  refine Finset.sum_nbij' (fun S => S.erase j) (fun R => insert j R) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSP, hiS, hjS⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, ?_, by simp⟩
    · exact (Finset.erase_subset _ _).trans (by intro x hx; simp)
    · intro hi
      exact hiS (Finset.mem_of_mem_erase hi)
  · intro R hR
    rcases Finset.mem_filter.mp hR with ⟨hRP, hiR, hjR⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, ?_, by simp⟩
    · intro x hx
      simp
    · simpa [hij] using hiR
  · intro S hS
    exact Finset.insert_erase (Finset.mem_filter.mp hS).2.2
  · intro R hR
    exact Finset.erase_insert (Finset.mem_filter.mp hR).2.2
  · intro S hS
    rw [Finset.insert_erase (Finset.mem_filter.mp hS).2.2]

private lemma shapleyValue_sum_without (v : Game N) (i : N) :
    shapleyValue N v i =
      ∑ R ∈ (coalitions N).filter (fun R => i ∉ R),
        weight N (R.card + 1) * (⇑v (insert i R) - ⇑v R) := by
  classical
  unfold shapleyValue
  rw [sum_filter_insert]
  apply Finset.sum_congr rfl
  intro R hR
  have hiR : i ∉ R := (Finset.mem_filter.mp hR).2
  simp [hiR]

theorem shapleyValue_nullPlayer : NullPlayer N (shapleyValue N) := by
  classical
  intro v i hnull
  unfold shapleyValue
  apply Finset.sum_eq_zero
  intro S hS
  have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
  have heq : ⇑v S = ⇑v (S.erase i) := by
    calc
      ⇑v S = ⇑v (insert i (S.erase i)) := by rw [Finset.insert_erase hiS]
      _ = ⇑v (S.erase i) := hnull (S.erase i) (by simp)
  rw [heq, sub_self, mul_zero]

theorem shapleyValue_additive : Additive N (shapleyValue N) := by
  classical
  intro v w i
  unfold shapleyValue
  simp only [Game.coe_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  ring

theorem shapleyValue_symmetric : Symmetric N (shapleyValue N) := by
  classical
  intro v i j h
  by_cases hij : i = j
  · subst j
    rfl
  · rw [shapleyValue_sum_without, shapleyValue_sum_without]
    let P := coalitions N
    let f₁ := fun R : Finset N =>
      weight N (R.card + 1) * (⇑v (insert i R) - ⇑v R)
    let f₂ := fun R : Finset N =>
      weight N (R.card + 1) * (⇑v (insert j R) - ⇑v R)
    rw [← Finset.sum_filter_add_sum_filter_not (s := P.filter (fun R => i ∉ R))
      (p := fun R => j ∈ R) f₁]
    rw [← Finset.sum_filter_add_sum_filter_not (s := P.filter (fun R => j ∉ R))
      (p := fun R => i ∈ R) f₂]
    simp only [Finset.filter_filter]
    rw [sum_filter_insert_of_not N i j hij f₁]
    rw [sum_filter_insert_of_not N j i (Ne.symm hij) f₂]
    simp only [f₁, f₂]
    simp only [and_comm]
    refine congrArg₂ (fun x y : ℝ => x + y) ?_ ?_
    · apply Finset.sum_congr rfl
      intro R hR
      rcases Finset.mem_filter.mp hR with ⟨hRP, hiR, hjR⟩
      simp [hiR, hjR, Finset.insert_comm, h R hiR hjR]
    · apply Finset.sum_congr rfl
      intro R hR
      rcases Finset.mem_filter.mp hR with ⟨hRP, hiR, hjR⟩
      have hv := h R hiR hjR
      simp [hv]

omit [DecidableEq N] in
private lemma weight_balance (k : ℕ) (hk : 0 < k)
    (hkn : k < Fintype.card N) :
    (k : ℝ) * weight N k =
      ((Fintype.card N - k : ℕ) : ℝ) * weight N (k + 1) := by
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hm1 : 1 ≤ Fintype.card N - k := Nat.sub_pos_of_lt hkn
  have hkfactNat : k.factorial = k * (k - 1).factorial := by
    have h := Nat.factorial_succ (k - 1)
    rw [Nat.sub_add_cancel hk1] at h
    exact h
  have hkfact : (k : ℝ) * ((k - 1).factorial : ℝ) = (k.factorial : ℝ) := by
    exact_mod_cast hkfactNat.symm
  have hmfactNat : (Fintype.card N - k).factorial =
      (Fintype.card N - k) * (Fintype.card N - k - 1).factorial := by
    have h := Nat.factorial_succ (Fintype.card N - k - 1)
    rw [Nat.sub_add_cancel hm1] at h
    exact h
  have hmfact : ((Fintype.card N - k : ℕ) : ℝ) *
      ((Fintype.card N - k - 1).factorial : ℝ) =
        ((Fintype.card N - k).factorial : ℝ) := by
    exact_mod_cast hmfactNat.symm
  have hsub : Fintype.card N - (k + 1) = Fintype.card N - k - 1 := by omega
  unfold weight
  rw [hsub]
  push_cast
  calc
    (k : ℝ) * (((k - 1).factorial : ℝ) *
        ((Fintype.card N - k).factorial : ℝ) / ((Fintype.card N).factorial : ℝ)) =
      ((k : ℝ) * ((k - 1).factorial : ℝ) *
        ((Fintype.card N - k).factorial : ℝ)) /
          ((Fintype.card N).factorial : ℝ) := by ring
    _ = ((k.factorial : ℝ) * ((Fintype.card N - k).factorial : ℝ)) /
        ((Fintype.card N).factorial : ℝ) := by rw [hkfact]
    _ = ((Fintype.card N - k : ℕ) : ℝ) *
        (((k.factorial : ℝ) * ((Fintype.card N - k - 1).factorial : ℝ)) /
          ((Fintype.card N).factorial : ℝ)) := by rw [← hmfact]; ring

omit [DecidableEq N] in
private lemma weight_top (hn : 0 < Fintype.card N) :
    (Fintype.card N : ℝ) * weight N (Fintype.card N) = 1 := by
  have hn1 : 1 ≤ Fintype.card N := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hfactNat : (Fintype.card N).factorial =
      Fintype.card N * (Fintype.card N - 1).factorial := by
    have h := Nat.factorial_succ (Fintype.card N - 1)
    rw [Nat.sub_add_cancel hn1] at h
    exact h
  have hfact : (Fintype.card N : ℝ) *
      ((Fintype.card N - 1).factorial : ℝ) = ((Fintype.card N).factorial : ℝ) := by
    exact_mod_cast hfactNat.symm
  unfold weight
  simp only [Nat.sub_self, Nat.factorial_zero]
  push_cast
  field_simp [card_factorial_cast_ne_zero N]
  exact hfact

theorem shapleyValue_efficient : Efficient N (shapleyValue N) := by
  classical
  intro v
  let P := coalitions N
  let n := Fintype.card N
  change (∑ i ∈ Finset.univ,
      ∑ S ∈ P.filter (fun S => i ∈ S),
        weight N S.card * (⇑v S - ⇑v (S.erase i))) = ⇑v Finset.univ
  have hA : (∑ i ∈ Finset.univ,
      ∑ S ∈ P.filter (fun S => i ∈ S), weight N S.card * ⇑v S) =
        ∑ S ∈ P, (S.card : ℝ) * weight N S.card * ⇑v S := by
    simpa [P, mul_assoc] using
      (sum_over_members N (fun S => weight N S.card * ⇑v S))
  have hB_reindex : (∑ i ∈ Finset.univ,
      ∑ S ∈ P.filter (fun S => i ∈ S), weight N S.card * ⇑v (S.erase i)) =
        ∑ i ∈ Finset.univ,
          ∑ T ∈ P.filter (fun T => i ∉ T),
            weight N (T.card + 1) * ⇑v T := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [sum_filter_insert N i (fun S => weight N S.card * ⇑v (S.erase i))]
    apply Finset.sum_congr rfl
    intro T hT
    have hiT : i ∉ T := (Finset.mem_filter.mp hT).2
    simp [hiT]
  have hB : (∑ i ∈ Finset.univ,
      ∑ T ∈ P.filter (fun T => i ∉ T), weight N (T.card + 1) * ⇑v T) =
        ∑ T ∈ P, ((n - T.card : ℕ) : ℝ) *
          weight N (T.card + 1) * ⇑v T := by
    simpa [P, n, mul_assoc] using
      (sum_over_nonmembers N (fun T => weight N (T.card + 1) * ⇑v T))
  have hsplit : (∑ i ∈ Finset.univ,
      ∑ S ∈ P.filter (fun S => i ∈ S),
        weight N S.card * (⇑v S - ⇑v (S.erase i))) =
      (∑ i ∈ Finset.univ,
        ∑ S ∈ P.filter (fun S => i ∈ S), weight N S.card * ⇑v S) -
      (∑ i ∈ Finset.univ,
        ∑ S ∈ P.filter (fun S => i ∈ S), weight N S.card * ⇑v (S.erase i)) := by
    calc
      _ = ∑ i ∈ Finset.univ,
          ((∑ S ∈ P.filter (fun S => i ∈ S), weight N S.card * ⇑v S) -
            (∑ S ∈ P.filter (fun S => i ∈ S), weight N S.card * ⇑v (S.erase i))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro S hS
        ring
      _ = _ := Finset.sum_sub_distrib _ _
  let c : Finset N → ℝ := fun S =>
    (S.card : ℝ) * weight N S.card - ((n - S.card : ℕ) : ℝ) * weight N (S.card + 1)
  calc
    _ = (∑ S ∈ P, (S.card : ℝ) * weight N S.card * ⇑v S) -
        (∑ S ∈ P, ((n - S.card : ℕ) : ℝ) * weight N (S.card + 1) * ⇑v S) := by
      rw [hsplit, hA, hB_reindex, hB]
    _ = ∑ S ∈ P, c S * ⇑v S := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro S hS
      simp only [c]
      ring
    _ = c Finset.univ * ⇑v Finset.univ := by
      apply Finset.sum_eq_single Finset.univ
      · intro S hS hSne
        by_cases hEmpty : S = ∅
        · subst S
          change c ∅ * (⇑v) ∅ = 0
          exact mul_eq_zero.mpr (Or.inr v.property)
        · have hkpos : 0 < S.card := by
            have hkne : S.card ≠ 0 := by
              intro hk
              exact hEmpty (Finset.card_eq_zero.mp hk)
            omega
          have hnlt : S.card < Fintype.card N := by
            simpa [Finset.card_univ] using
              (Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hSne))
          have hbal := weight_balance N S.card hkpos hnlt
          have hcoef : c S = 0 := by
            simp only [c, n]
            rw [hbal]
            ring
          rw [hcoef]
          simp
      · intro htop
        simp [P] at htop
    _ = ⇑v Finset.univ := by
      by_cases hn : Fintype.card N = 0
      · have huniv : (Finset.univ : Finset N) = ∅ := by
          apply Finset.card_eq_zero.mp
          simp [hn]
        rw [huniv]
        calc
          c ∅ * (⇑v) ∅ = 0 := mul_eq_zero.mpr (Or.inr v.property)
          _ = (⇑v) ∅ := v.property.symm
      · have hnpos : 0 < Fintype.card N := Nat.pos_of_ne_zero hn
        have htop : c Finset.univ = 1 := by
          simp only [c, n, Finset.card_univ, Nat.sub_self, Nat.cast_zero,
            zero_mul, sub_zero]
          exact weight_top N hnpos
        rw [htop]
        simp

end ShapleyValue
