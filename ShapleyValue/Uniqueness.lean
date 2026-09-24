import ShapleyValue.Basic
import ShapleyValue.Existence
import Mathlib.Tactic

namespace ShapleyValue

variable (N : Type*) [Fintype N] [DecidableEq N]

open scoped BigOperators

omit [Fintype N] [DecidableEq N] in
instance : AddCommMonoid (Game N) where
  add_assoc v w x := by
    apply DFunLike.ext
    intro S
    simp only [Game.coe_add, add_assoc]
  zero_add v := by
    apply DFunLike.ext
    intro S
    simp only [Game.coe_add, Game.coe_zero, zero_add]
  add_zero v := by
    apply DFunLike.ext
    intro S
    simp only [Game.coe_add, Game.coe_zero, add_zero]
  nsmul := nsmulRec
  add_comm v w := by
    apply DFunLike.ext
    intro S
    simp only [Game.coe_add, add_comm]

omit [Fintype N] [DecidableEq N] in
theorem Game.coe_sum (s : Finset (Finset N)) (g : Finset N → Game N)
    (Q : Finset N) : ⇑(∑ T ∈ s, g T) Q = ∑ T ∈ s, ⇑(g T) Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Game.coe_zero]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Game.coe_add, ih]

noncomputable def unanimityGame (T : Finset N) : Game N :=
  ⟨fun S => if T ⊆ S ∧ T.Nonempty then (1 : ℝ) else 0, by
    classical
    by_cases hT : T.Nonempty
    · have hnot : ¬ T ⊆ ∅ := by
        intro hsub
        have hEq : T = ∅ := Finset.subset_empty.mp hsub
        subst T
        simp at hT
      simp [hnot, hT]
    · simp [hT]⟩

omit [Fintype N] in
@[simp] theorem coe_unanimity (T S : Finset N) :
    ⇑(unanimityGame N T) S = (if T ⊆ S ∧ T.Nonempty then (1 : ℝ) else 0) := rfl

noncomputable def mobiusCoeff (v : Game N) (T : Finset N) : ℝ :=
  ∑ S ∈ T.powerset, (-1 : ℝ)^(T.card - S.card) * ⇑v S

theorem valueOn_unanimity (ψ : Game N → N → ℝ) (hE : Efficient N ψ)
    (hS : Symmetric N ψ) (hN : NullPlayer N ψ) (T : Finset N)
    (hT : T.Nonempty) (c : ℝ) (i : N) :
    ψ (c • unanimityGame N T) i = if i ∈ T then c / (T.card : ℝ) else 0 := by
  classical
  let w : Game N := c • unanimityGame N T
  have hi_not_null (k : N) (hk : k ∉ T) : ψ w k = 0 := by
    apply hN w k
    intro S hkS
    change ⇑(c • unanimityGame N T) (insert k S) =
      ⇑(c • unanimityGame N T) S
    rw [Game.coe_smul, coe_unanimity, Game.coe_smul, coe_unanimity]
    have hsub : T ⊆ insert k S ↔ T ⊆ S :=
      Finset.subset_insert_iff_of_notMem hk
    have hiff : (T ⊆ insert k S ∧ T.Nonempty) ↔ (T ⊆ S ∧ T.Nonempty) :=
      and_congr hsub Iff.rfl
    by_cases hr : T ⊆ S ∧ T.Nonempty
    · have hl := hiff.mpr hr
      simp [hr, hl]
    · have hl : ¬ (T ⊆ insert k S ∧ T.Nonempty) := fun h => hr (hiff.mp h)
      simp [hr, hl]
  have hsym (a b : N) (ha : a ∈ T) (hb : b ∈ T) : ψ w a = ψ w b := by
    apply hS w a b
    intro S haS hbS
    by_cases hab : a = b
    · subst b
      rfl
    · change ⇑(c • unanimityGame N T) (insert a S) =
        ⇑(c • unanimityGame N T) (insert b S)
      rw [Game.coe_smul, coe_unanimity, Game.coe_smul, coe_unanimity]
      have hnotA : ¬ T ⊆ insert a S := by
        intro hsub
        have : b ∈ insert a S := hsub hb
        simp [Ne.symm hab, hbS] at this
      have hnotB : ¬ T ⊆ insert b S := by
        intro hsub
        have : a ∈ insert b S := hsub ha
        simp [hab, haS] at this
      have hfalseA : ¬ (T ⊆ insert a S ∧ T.Nonempty) := fun h => hnotA h.1
      have hfalseB : ¬ (T ⊆ insert b S ∧ T.Nonempty) := fun h => hnotB h.1
      simp [hfalseA, hfalseB]
  have hsumNot : (∑ k ∈ Finset.univ.filter (fun k : N => k ∉ T), ψ w k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact hi_not_null k ((Finset.mem_filter.mp hk).2)
  have htotal : (∑ k, ψ w k) = c := by
    have heff := hE w
    have hwuniv : ⇑w Finset.univ = c := by
      simp [w, Game.coe_smul, coe_unanimity, hT]
    calc
      (∑ k, ψ w k) = ⇑w Finset.univ := heff
      _ = c := hwuniv
  have hsplit :
      (∑ k, ψ w k) = (∑ k ∈ T, ψ w k) +
        ∑ k ∈ Finset.univ.filter (fun k : N => k ∉ T), ψ w k := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun k : N => k ∈ T) (f := fun k => ψ w k)]
    simp
  by_cases hi : i ∈ T
  · have hsumT :
        (∑ k ∈ T, ψ w k) = (T.card : ℝ) * ψ w i := by
      calc
        ∑ k ∈ T, ψ w k = ∑ k ∈ T, ψ w i := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hsym k i hk hi
        _ = (T.card : ℝ) * ψ w i := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
    have hcard : (T.card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hT)
    have hprod : (T.card : ℝ) * ψ w i = c := by
      calc
        (T.card : ℝ) * ψ w i = ∑ k ∈ T, ψ w k := hsumT.symm
        _ = ∑ k, ψ w k := by
          calc
            _ = (∑ k ∈ T, ψ w k) +
                ∑ k ∈ Finset.univ.filter (fun k : N => k ∉ T), ψ w k := by
                  simp [hsumNot]
            _ = ∑ k, ψ w k := hsplit.symm
        _ = c := htotal
    have hvalue : ψ w i = c / (T.card : ℝ) := by
      field_simp [hcard]
      nlinarith [hprod]
    simp [w, hi, hvalue]
  · simp [w, hi, hi_not_null i hi]

omit [Fintype N] [DecidableEq N] in
theorem alt_sum_powerset (P : Finset N) (hP : P.Nonempty) :
    ∑ R ∈ P.powerset, (-1 : ℝ)^(R.card) = 0 := by
  classical
  exact_mod_cast (Finset.sum_powerset_neg_one_pow_card_of_nonempty hP)

omit [Fintype N] in
theorem inner_mobius (S Q : Finset N) (hSQ : S ⊆ Q) (hneq : S ≠ Q)
    (hS : S.Nonempty) :
    ∑ T ∈ (Q.powerset).filter (fun T => S ⊆ T ∧ T.Nonempty),
      (-1 : ℝ)^(T.card - S.card) = 0 := by
  classical
  let D := (Q.powerset).filter (fun T => S ⊆ T ∧ T.Nonempty)
  let E := (Q \ S).powerset
  have hnonempty : (Q \ S).Nonempty := by
    apply Finset.sdiff_nonempty.mpr
    intro hQS
    exact hneq (Finset.Subset.antisymm hSQ hQS)
  have hsum :
      (∑ T ∈ D, (-1 : ℝ)^(T.card - S.card)) =
        ∑ U ∈ E, (-1 : ℝ)^(U.card) := by
    unfold D E
    refine Finset.sum_nbij' (fun T => T \ S) (fun U => S ∪ U) ?_ ?_ ?_ ?_ ?_
    · intro T hT
      rcases Finset.mem_filter.mp hT with ⟨hTQ, hST, hTne⟩
      apply Finset.mem_powerset.mpr
      intro x hx
      rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxS⟩
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hTQ) hxT, hxS⟩
    · intro U hU
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_union.mp hx with hxS | hxU
        · exact hSQ hxS
        · exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hxU)).1
      · refine ⟨?_, ?_⟩
        · intro x hx
          exact Finset.mem_union.mpr (Or.inl hx)
        · rcases hS with ⟨x, hx⟩
          exact ⟨x, Finset.mem_union.mpr (Or.inl hx)⟩
    · intro T hT
      have hST : S ⊆ T := (Finset.mem_filter.mp hT).2.1
      exact Finset.union_sdiff_of_subset hST
    · intro U hU
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxS | hxU, hxnotS⟩
        · exact False.elim (hxnotS hxS)
        · exact hxU
      · intro hxU
        exact ⟨Or.inr hxU, (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hxU)).2⟩
    · intro T hT
      have hST : S ⊆ T := (Finset.mem_filter.mp hT).2.1
      rw [Finset.card_sdiff_of_subset hST]
  rw [hsum]
  exact alt_sum_powerset N (Q \ S) hnonempty

theorem mobius_pointwise (v : Game N) (Q : Finset N) :
    ⇑v Q =
      ∑ T ∈ (Finset.univ.powerset).filter (fun T => T.Nonempty ∧ T ⊆ Q),
        mobiusCoeff N v T := by
  classical
  let U : Finset (Finset N) := Finset.univ.powerset
  let A : Finset (Finset N) := U.filter (fun T => T.Nonempty ∧ T ⊆ Q)
  let B : Finset (Finset N) := Q.powerset
  let C : Finset N → ℝ := fun S =>
    ∑ T ∈ A.filter (fun T => S ⊆ T), (-1 : ℝ)^(T.card - S.card)
  have hfilter (S : Finset N) :
      A.filter (fun T => S ⊆ T) =
        B.filter (fun T => S ⊆ T ∧ T.Nonempty) := by
    ext T
    simp [A, B, U, and_assoc, and_left_comm, and_comm]
  have hexpand :
      (∑ T ∈ A, mobiusCoeff N v T) =
        ∑ T ∈ A, ∑ S ∈ B,
          (if S ⊆ T then (-1 : ℝ)^(T.card - S.card) * ⇑v S else 0) := by
    apply Finset.sum_congr rfl
    intro T hT
    have hTQ : T ⊆ Q := (Finset.mem_filter.mp hT).2.2
    unfold mobiusCoeff
    have hset : B.filter (fun S => S ⊆ T) = T.powerset := by
      ext S
      simp only [B, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨hSQ, hST⟩
        exact hST
      · intro hST
        exact ⟨hST.trans hTQ, hST⟩
    calc
      (∑ S ∈ T.powerset, (-1 : ℝ)^(T.card - S.card) * ⇑v S) =
          ∑ S ∈ B.filter (fun S => S ⊆ T),
            (-1 : ℝ)^(T.card - S.card) * ⇑v S := by rw [hset]
      _ = ∑ S ∈ B,
          (if S ⊆ T then (-1 : ℝ)^(T.card - S.card) * ⇑v S else 0) := by
            rw [Finset.sum_filter]
  have hfactor (S : Finset N) :
      (∑ T ∈ A, if S ⊆ T then (-1 : ℝ)^(T.card - S.card) * ⇑v S else 0) =
        ⇑v S * C S := by
    calc
      _ = ∑ T ∈ A, (if S ⊆ T then (-1 : ℝ)^(T.card - S.card) else 0) * ⇑v S := by
        apply Finset.sum_congr rfl
        intro T hT
        by_cases hST : S ⊆ T <;> simp [hST]
      _ = (∑ T ∈ A, if S ⊆ T then (-1 : ℝ)^(T.card - S.card) else 0) * ⇑v S := by
        rw [Finset.sum_mul]
      _ = (∑ T ∈ A.filter (fun T => S ⊆ T), (-1 : ℝ)^(T.card - S.card)) * ⇑v S := by
        rw [← Finset.sum_filter]
      _ = ⇑v S * C S := by
        simp only [C]
        ring
  have hsumfactor :
      (∑ S ∈ B, ⇑v S * C S) = ⇑v Q * C Q := by
    apply Finset.sum_eq_single Q
    · intro S hS hSneQ
      by_cases hSempty : S = ∅
      · subst S
        change ⇑v ∅ * C ∅ = 0
        exact mul_eq_zero.mpr (Or.inl v.empty_val)
      · have hSnon : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSempty
        have hSQ : S ⊆ Q := Finset.mem_powerset.mp hS
        have hCzero : C S = 0 := by
          change (∑ T ∈ A.filter (fun T => S ⊆ T),
            (-1 : ℝ)^(T.card - S.card)) = 0
          rw [hfilter]
          exact inner_mobius N S Q hSQ hSneQ hSnon
        simp [hCzero]
    · intro hQnot
      have : Q ∈ B := by simp [B]
      exact (hQnot this).elim
  have hCQ : C Q = if Q.Nonempty then 1 else 0 := by
    by_cases hQ : Q.Nonempty
    · have hset : B.filter (fun T => Q ⊆ T ∧ T.Nonempty) = {Q} := by
        ext T
        simp only [B, Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
        constructor
        · rintro ⟨hTQ, hQT, hTne⟩
          have hEq : T = Q := Finset.Subset.antisymm hTQ hQT
          exact hEq
        · intro hEq
          subst T
          exact ⟨subset_rfl, subset_rfl, hQ⟩
      change (∑ T ∈ A.filter (fun T => Q ⊆ T),
        (-1 : ℝ)^(T.card - Q.card)) = _
      rw [hfilter, hset]
      simp [hQ]
    · have hset : B.filter (fun T => Q ⊆ T ∧ T.Nonempty) = ∅ := by
        ext T
        constructor
        · intro hmem
          rcases Finset.mem_filter.mp hmem with ⟨hTB, hpred⟩
          rcases hpred with ⟨hQT, hTne⟩
          have hTQ : T ⊆ Q := Finset.mem_powerset.mp hTB
          have hEq : T = Q := Finset.Subset.antisymm hTQ hQT
          subst T
          exact False.elim (hQ hTne)
        · intro hmem
          simp at hmem
      change (∑ T ∈ A.filter (fun T => Q ⊆ T),
        (-1 : ℝ)^(T.card - Q.card)) = _
      rw [hfilter, hset]
      simp [hQ]
  have hswapfactor :
      (∑ S ∈ B, ∑ T ∈ A,
        (if S ⊆ T then (-1 : ℝ)^(T.card - S.card) * ⇑v S else 0)) =
        ∑ S ∈ B, ⇑v S * C S := by
    apply Finset.sum_congr rfl
    intro S hS
    exact hfactor S
  have hmain : ⇑v Q * C Q = ⇑v Q := by
    by_cases hQ : Q.Nonempty
    · rw [hCQ]
      simp [hQ]
    · have hQempty : Q = ∅ := by simpa using hQ
      rw [hCQ]
      simp only [if_neg hQ, mul_zero]
      rw [hQempty]
      exact v.empty_val.symm
  have hsumA : (∑ T ∈ A, mobiusCoeff N v T) = ⇑v Q := by
    calc
      (∑ T ∈ A, mobiusCoeff N v T) =
          ∑ S ∈ B, ∑ T ∈ A,
            (if S ⊆ T then (-1 : ℝ)^(T.card - S.card) * ⇑v S else 0) := by
              rw [hexpand, Finset.sum_comm]
      _ = ∑ S ∈ B, ⇑v S * C S := hswapfactor
      _ = ⇑v Q * C Q := hsumfactor
      _ = ⇑v Q := hmain
  exact hsumA.symm

theorem mobius_decomposition (v : Game N) :
    v = ∑ T ∈ (Finset.univ.powerset).filter (fun T => T.Nonempty),
      (mobiusCoeff N v T) • unanimityGame N T := by
  classical
  apply DFunLike.ext
  intro Q
  rw [Game.coe_sum]
  simp_rw [Game.coe_smul, coe_unanimity]
  calc
    ⇑v Q =
      ∑ T ∈ (Finset.univ.powerset).filter (fun T => T.Nonempty ∧ T ⊆ Q),
        mobiusCoeff N v T := mobius_pointwise N v Q
    _ =
      ∑ T ∈ (Finset.univ.powerset).filter (fun T => T.Nonempty),
        mobiusCoeff N v T * (if T ⊆ Q ∧ T.Nonempty then (1 : ℝ) else 0) := by
      let P : Finset (Finset N) :=
        (Finset.univ.powerset).filter (fun T => T.Nonempty)
      have hset :
          (Finset.univ.powerset).filter (fun T => T.Nonempty ∧ T ⊆ Q) =
            P.filter (fun T => T ⊆ Q) := by
        ext T
        simp [P]
      calc
        (∑ T ∈ (Finset.univ.powerset).filter
            (fun T => T.Nonempty ∧ T ⊆ Q), mobiusCoeff N v T) =
            ∑ T ∈ P.filter (fun T => T ⊆ Q), mobiusCoeff N v T := by rw [hset]
        _ = ∑ T ∈ P, if T ⊆ Q then mobiusCoeff N v T else 0 := by
          rw [Finset.sum_filter]
        _ = ∑ T ∈ P,
            if T ⊆ Q ∧ T.Nonempty then mobiusCoeff N v T else 0 := by
          apply Finset.sum_congr rfl
          intro T hT
          have hTne : T.Nonempty := (Finset.mem_filter.mp hT).2
          by_cases hTQ : T ⊆ Q <;> simp [hTne, hTQ]
        _ = ∑ T ∈ P, mobiusCoeff N v T *
            (if T ⊆ Q ∧ T.Nonempty then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro T hT
          by_cases hcond : T ⊆ Q ∧ T.Nonempty <;> simp [hcond]

omit [Fintype N] [DecidableEq N] in
theorem additive_sum {ι : Type*} (ψ : Game N → N → ℝ) (hA : Additive N ψ)
    (s : Finset ι) (g : ι → Game N) (i : N) :
    ψ (∑ T ∈ s, g T) i = ∑ T ∈ s, ψ (g T) i := by
  classical
  have hzero : ψ (0 : Game N) i = 0 := by
    have h := hA (0 : Game N) 0 i
    simp only [zero_add] at h
    linarith
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [hA, ih]

theorem value_eq_of_axioms (ψ : Game N → N → ℝ) (hE : Efficient N ψ)
    (hS : Symmetric N ψ) (hN : NullPlayer N ψ) (hA : Additive N ψ)
    (v : Game N) (i : N) :
    ψ v i =
      ∑ T ∈ (Finset.univ.powerset).filter (fun T => T.Nonempty ∧ i ∈ T),
        mobiusCoeff N v T / (T.card : ℝ) := by
  classical
  conv_lhs => rw [mobius_decomposition N v]
  calc
    ψ (∑ T ∈ (Finset.univ.powerset).filter (fun T => T.Nonempty),
        (mobiusCoeff N v T) • unanimityGame N T) i =
      ∑ T ∈ (Finset.univ.powerset).filter (fun T => T.Nonempty),
        ψ ((mobiusCoeff N v T) • unanimityGame N T) i := by
          exact additive_sum N ψ hA _ _ i
    _ =
      ∑ T ∈ (Finset.univ.powerset).filter (fun T => T.Nonempty),
        (if i ∈ T then mobiusCoeff N v T / (T.card : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro T hT
          exact valueOn_unanimity N ψ hE hS hN T
            (Finset.mem_filter.mp hT).2 (mobiusCoeff N v T) i
    _ =
      ∑ T ∈ (Finset.univ.powerset).filter (fun T => T.Nonempty ∧ i ∈ T),
        mobiusCoeff N v T / (T.card : ℝ) := by
          let P : Finset (Finset N) :=
            (Finset.univ.powerset).filter (fun T => T.Nonempty)
          have hset :
              P.filter (fun T => i ∈ T) =
                (Finset.univ.powerset).filter (fun T => T.Nonempty ∧ i ∈ T) := by
            ext T
            simp [P]
          calc
            (∑ T ∈ P,
                (if i ∈ T then mobiusCoeff N v T / (T.card : ℝ) else 0)) =
                ∑ T ∈ P.filter (fun T => i ∈ T),
                  mobiusCoeff N v T / (T.card : ℝ) := by
                    rw [← Finset.sum_filter]
            _ = _ := by rw [hset]

theorem shapleyValue_unique (ψ : Game N → N → ℝ) (hE : Efficient N ψ)
    (hS : Symmetric N ψ) (hN : NullPlayer N ψ) (hA : Additive N ψ) :
    ψ = shapleyValue N := by
  funext v i
  rw [value_eq_of_axioms N ψ hE hS hN hA v i,
    value_eq_of_axioms N (shapleyValue N) (shapleyValue_efficient N)
      (shapleyValue_symmetric N) (shapleyValue_nullPlayer N)
      (shapleyValue_additive N) v i]

theorem shapley_characterization (ψ : Game N → N → ℝ) :
    (Efficient N ψ ∧ Symmetric N ψ ∧ NullPlayer N ψ ∧ Additive N ψ) ↔
      ψ = shapleyValue N := by
  constructor
  · rintro ⟨hE, hS, hN, hA⟩
    exact shapleyValue_unique N ψ hE hS hN hA
  · intro h
    subst h
    exact ⟨shapleyValue_efficient N, shapleyValue_symmetric N,
      shapleyValue_nullPlayer N, shapleyValue_additive N⟩

end ShapleyValue
