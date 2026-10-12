import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.EquivFin

/-!
# Integer general position and spanning over a characteristic-zero field

Every square matrix obtained by selecting `k` distinct rows has nonzero integer
determinant. Its determinant remains nonzero after casting to any
characteristic-zero field. Consequently, any selected set with at least `k`
rows spans all longitudinal directions over that field.

This condition does not imply that every row is nonzero when there are fewer
than `k` rows available; no such conclusion is asserted here.
-/

namespace GeneralizedLogarithms

noncomputable section

/-- Every selection of `k` distinct integer rows gives a nonsingular matrix. -/
def IntegerGeneralPosition {k m : ℕ} (a : Fin m → Fin k → ℤ) : Prop :=
  ∀ e : Fin k ↪ Fin m, Matrix.det (fun i r => a (e i) r) ≠ 0

namespace IntegerGeneralPosition

variable (K : Type*) [Field K] [CharZero K] {k m : ℕ}

/-- An integer determinant remains nonzero in characteristic zero. -/
theorem det_cast_ne_zero (A : Matrix (Fin k) (Fin k) ℤ) (hA : A.det ≠ 0) :
    Matrix.det (fun i r => (A i r : K)) ≠ 0 := by
  change (A.map fun z => (z : K)).det ≠ 0
  rw [← Int.cast_det]
  exact Int.cast_ne_zero.mpr hA

/-- Each square selection spans the complete longitudinal vector space. -/
theorem selected_square_rows_span (a : Fin m → Fin k → ℤ)
    (ha : IntegerGeneralPosition a) (e : Fin k ↪ Fin m) :
    Submodule.span K (Set.range (fun i r => (a (e i) r : K))) = ⊤ := by
  have hind : LinearIndependent K (fun i r => (a (e i) r : K)) :=
    Matrix.linearIndependent_rows_of_det_ne_zero
      (det_cast_ne_zero K (fun i r => a (e i) r) (ha e))
  exact hind.span_eq_top_of_card_eq_finrank' (by simp)

/-- A sufficiently large selected finite set spans after casting to any
characteristic-zero field. The rows are enumerated exactly as required by the
function-field monomial constancy theorem. -/
theorem selected_rows_span (a : Fin m → Fin k → ℤ)
    (ha : IntegerGeneralPosition a) (J : Finset (Fin m)) (hJ : k ≤ J.card) :
    Submodule.span K (Set.range
      (fun i : Fin J.card => fun r => (a (J.equivFin.symm i) r : K))) = ⊤ := by
  classical
  let e : Fin k ↪ Fin m :=
    ((Fin.castLEEmb hJ).trans J.equivFin.symm.toEmbedding).trans
      (Function.Embedding.subtype (fun i => i ∈ J))
  have hspan := selected_square_rows_span K a ha e
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Fin.castLE hJ i, rfl⟩

end IntegerGeneralPosition
end
end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.IntegerGeneralPosition.det_cast_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.IntegerGeneralPosition.det_cast_ne_zero

/-- info: 'GeneralizedLogarithms.IntegerGeneralPosition.selected_rows_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.IntegerGeneralPosition.selected_rows_span
