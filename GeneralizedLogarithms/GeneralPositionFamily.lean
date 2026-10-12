import GeneralizedLogarithms.GeneralPositionSelection
import GeneralizedLogarithms.IntegerGeneralPosition
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Finset.Max

/-!
# Recursive exceptional forms in integer general position

Failure at one fixed exponent and the positive lower-rank induction hypotheses
supply a sequence of strict exceptional forms. Every next height may be chosen
as an arbitrary function of the earlier finite family. Avoidance of all small
earlier spans implies rational independence of every selection of at most `k`
rows and hence the integer determinant condition used by the curve theorem.
-/

namespace GeneralizedLogarithms.GeneralPositionFamily

noncomputable section

/-- Dependent finite histories can be assembled into one compatible sequence. -/
theorem exists_recursive_sequence {X : Type*}
    (P : (n : ℕ) → (Fin n → X) → X → Prop)
    (hP : ∀ n previous, ∃ x, P n previous x) :
    ∃ f : ℕ → X, ∀ n, P n (fun i : Fin n => f i.val) (f n) := by
  classical
  let next (n : ℕ) (previous : Fin n → X) : X := (hP n previous).choose
  let history : (n : ℕ) → Fin n → X :=
    Nat.rec (motive := fun n => Fin n → X) Fin.elim0
      (fun n previous => Fin.snoc previous (next n previous))
  let f (n : ℕ) := next n (history n)
  have heq : ∀ n (i : Fin n), history n i = f i.val := by
    intro n
    induction n with
    | zero => intro i; exact Fin.elim0 i
    | succ n ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [history, Fin.snoc_last, Fin.val_last, f]
      · simpa only [history, Fin.snoc_castSucc, Fin.val_castSucc] using ih j
  refine ⟨f, fun n => ?_⟩
  have hhistory : history n = (fun i : Fin n => f i.val) := funext (heq n)
  rw [← hhistory]
  exact (hP n (history n)).choose_spec

variable {k : ℕ}

/-- Prefix-index avoidance also avoids every finite set of earlier natural
indices. Only cardinality and the earlier-index property are needed. -/
theorem not_mem_earlier_span
    (a : ℕ → Fin k → ℤ)
    (hescape : ∀ n (s : Finset (Fin n)), s.card < k →
      (fun j => (a n j : ℚ)) ∉ Submodule.span ℚ
        (Set.range (fun i : s => fun j => (a i.val.val j : ℚ))))
    (n : ℕ) (s : Finset ℕ) (hcard : s.card < k) (hlt : ∀ i ∈ s, i < n) :
    (fun j => (a n j : ℚ)) ∉ Submodule.span ℚ
      ((fun i j => (a i j : ℚ)) '' (s : Set ℕ)) := by
  classical
  let t : Finset (Fin n) := Finset.univ.filter (fun i => i.val ∈ s)
  let e : t → s := fun i => ⟨i.val.val, (Finset.mem_filter.mp i.property).2⟩
  have he : Function.Injective e := by
    intro i j h
    apply Subtype.ext
    apply Fin.ext
    exact congrArg Subtype.val h
  have htcard : t.card ≤ s.card := by simpa using Fintype.card_le_of_injective e he
  intro hx
  apply hescape n t (htcard.trans_lt hcard)
  apply Submodule.span_mono (show
    ((fun i j => (a i j : ℚ)) '' (s : Set ℕ)) ⊆
      Set.range (fun i : t => fun j => (a i.val.val j : ℚ)) from ?_) hx
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨⟨⟨i, hlt i hi⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩, rfl⟩

/-- Removing the largest index reduces independence to the next-row escape
property. This also covers selections smaller than the ambient rank. -/
theorem independent_small_selection
    (a : ℕ → Fin k → ℤ)
    (hescape : ∀ n (s : Finset (Fin n)), s.card < k →
      (fun j => (a n j : ℚ)) ∉ Submodule.span ℚ
        (Set.range (fun i : s => fun j => (a i.val.val j : ℚ))))
    (s : Finset ℕ) (hcard : s.card ≤ k) :
    LinearIndepOn ℚ (fun i j => (a i j : ℚ)) (s : Set ℕ) := by
  classical
  revert hcard
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert n s hlt ih =>
    intro hcard
    have hn : n ∉ s := fun hn => (lt_irrefl n) (hlt n hn)
    have hs : s.card < k := by
      rw [Finset.card_insert_of_notMem hn] at hcard
      omega
    rw [Finset.coe_insert, linearIndepOn_insert hn]
    exact ⟨ih (Nat.le_of_lt hs), not_mem_earlier_span a hescape n s hs hlt⟩

abbrev Form (k : ℕ) := ℤ × (Fin k → ℤ)

/-- The exceptional sequence carries its recursive height requirements and
the stronger small-selection independence property. No rank-zero induction
input is required. -/
theorem exists_exceptional_sequence
    (α : Fin k → ℚ) (hα : ∀ j, 0 < α j) (hind : MultiplicativelyIndependent α)
    (hlower : ∀ r : ℕ, 0 < r → r < k → ∀ β : Fin r → ℚ,
      (∀ s, 0 < β s) → MultiplicativelyIndependent β → EventualLinearFormLowerBound β)
    (ν : ℝ) (hν : (k : ℝ) < ν)
    (hfailure : ¬ ∃ H₀ : ℕ, ∀ (p : ℤ) (a : Fin k → ℤ),
      H₀ ≤ coefficientHeight p a →
        (coefficientHeight p a : ℝ) ^ (-ν) ≤ |linearForm α p a|)
    (T : (n : ℕ) → (Fin n → Form k) → ℕ) :
    ∃ f : ℕ → Form k,
      (∀ n, T n (fun i : Fin n => f i.val) ≤ coefficientHeight (f n).1 (f n).2 ∧
        (f n).2 ≠ 0 ∧
        |linearForm α (f n).1 (f n).2| < (coefficientHeight (f n).1 (f n).2 : ℝ) ^ (-ν)) ∧
      ∀ s : Finset ℕ, s.card ≤ k →
        LinearIndepOn ℚ (fun i j => ((f i).2 j : ℚ)) (s : Set ℕ) := by
  let P (n : ℕ) (previous : Fin n → Form k) (x : Form k) : Prop :=
    T n previous ≤ coefficientHeight x.1 x.2 ∧ x.2 ≠ 0 ∧
      |linearForm α x.1 x.2| < (coefficientHeight x.1 x.2 : ℝ) ^ (-ν) ∧
      ∀ s : Finset (Fin n), s.card < k → (fun j => (x.2 j : ℚ)) ∉
        Submodule.span ℚ (Set.range (fun i : s => fun j => ((previous i.val).2 j : ℚ)))
  have hP : ∀ n previous, ∃ x, P n previous x := by
    intro n previous
    obtain ⟨p, a, hH, ha, hbad, hs⟩ :=
      GeneralPositionSelection.exceptional_form_outside_small_spans α hα hind hlower ν hν
        hfailure (fun i => (previous i).2) (T n previous)
    exact ⟨(p, a), hH, ha, hbad, hs⟩
  obtain ⟨f, hf⟩ := exists_recursive_sequence P hP
  refine ⟨f, fun n => ⟨(hf n).1, (hf n).2.1, (hf n).2.2.1⟩, ?_⟩
  exact independent_small_selection (fun n => (f n).2) (fun n => (hf n).2.2.2)

/-- Any prescribed finite number of strict exceptional forms can be selected
in actual integer general position, with nonzero rows and arbitrary recursive
height thresholds depending on the previous forms. -/
theorem exists_exceptional_family
    (α : Fin k → ℚ) (hα : ∀ j, 0 < α j) (hind : MultiplicativelyIndependent α)
    (hlower : ∀ r : ℕ, 0 < r → r < k → ∀ β : Fin r → ℚ,
      (∀ s, 0 < β s) → MultiplicativelyIndependent β → EventualLinearFormLowerBound β)
    (ν : ℝ) (hν : (k : ℝ) < ν)
    (hfailure : ¬ ∃ H₀ : ℕ, ∀ (p : ℤ) (a : Fin k → ℤ),
      H₀ ≤ coefficientHeight p a →
        (coefficientHeight p a : ℝ) ^ (-ν) ≤ |linearForm α p a|)
    (T : (n : ℕ) → (Fin n → Form k) → ℕ) (m : ℕ) :
    ∃ (p : Fin m → ℤ) (a : Fin m → Fin k → ℤ),
      IntegerGeneralPosition a ∧
      (∀ i, a i ≠ 0) ∧
      (∀ i, |linearForm α (p i) (a i)| < (coefficientHeight (p i) (a i) : ℝ) ^ (-ν)) ∧
      (∀ i : Fin m, T i.val (fun j : Fin i.val =>
        (p ⟨j.val, j.isLt.trans i.isLt⟩, a ⟨j.val, j.isLt.trans i.isLt⟩)) ≤
          coefficientHeight (p i) (a i)) ∧
      ∀ n, n ≤ k → ∀ e : Fin n ↪ Fin m,
        LinearIndependent ℚ (fun i j => (a (e i) j : ℚ)) := by
  classical
  obtain ⟨f, hf, hsmall⟩ := exists_exceptional_sequence α hα hind hlower ν hν hfailure T
  let p : Fin m → ℤ := fun i => (f i.val).1
  let a : Fin m → Fin k → ℤ := fun i => (f i.val).2
  have hli (n : ℕ) (hn : n ≤ k) (e : Fin n ↪ Fin m) :
      LinearIndependent ℚ (fun i j => (a (e i) j : ℚ)) := by
    let s : Finset ℕ := Finset.univ.image (fun i : Fin n => (e i).val)
    have hs : s.card ≤ k := (Finset.card_image_le.trans (by simp)).trans hn
    have hi := hsmall s hs
    let g : Fin n → s := fun i =>
      ⟨(e i).val, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    have hg : Function.Injective g := by
      intro i j h
      apply e.injective
      exact Fin.ext (congrArg Subtype.val h)
    exact hi.comp g hg
  refine ⟨p, a, ?_, fun i => (hf i.val).2.1, fun i => (hf i.val).2.2,
    fun i => (hf i.val).1, hli⟩
  intro e
  have hdet : Matrix.det (fun i j => (a (e i) j : ℚ)) ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp (hli k le_rfl e))).ne_zero
  intro hzero
  let A : Matrix (Fin k) (Fin k) ℤ := Matrix.of (fun i j => a (e i) j)
  have hA : A.det = 0 := hzero
  have hcast : (A.det : ℚ) ≠ 0 := by
    rw [Int.cast_det]
    exact hdet
  exact hcast (by rw [hA, Int.cast_zero])

end
end GeneralizedLogarithms.GeneralPositionFamily

/-- info: 'GeneralizedLogarithms.GeneralPositionFamily.exists_exceptional_sequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.GeneralPositionFamily.exists_exceptional_sequence

/-- info: 'GeneralizedLogarithms.GeneralPositionFamily.exists_exceptional_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.GeneralPositionFamily.exists_exceptional_family
