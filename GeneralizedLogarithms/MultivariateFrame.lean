import LogIrrationalityMeasure.Jets.NormalFrameBasis
import GeneralizedLogarithms.NormalBasisRigidity

/-!
# A frame with several logarithmic directions

The ambient coordinates are `Fin k ⊕ Fin m`: the left summand records the
longitudinal coordinates and the right summand the transverse coordinates.
For nonzero `y r` and an exponent matrix `a`, the frame is

* `D_r = y_r eY_r + ∑ i, a_i_r eX_i`;
* `eX_i` in the transverse directions.

The inverse frame coordinates are proved explicitly. A transverse direction
belonging to every normal basis then gives its logarithmic differential
relation on the tangent kernel of the normal quotient. The final result
handles an entire mandatory set of transverse directions simultaneously.
-/

namespace GeneralizedLogarithms

noncomputable section

open Module
open LogIrrationalityMeasure.LogExponent.NormalBasisRigidity

namespace MultivariateFrame

variable {K : Type*} [Field K] {k m : ℕ}
variable (a : Fin m → Fin k → K) (y : Fin k → K) (hy : ∀ r, y r ≠ 0)

/-- Change from logarithmic frame coordinates to ordinary coordinates. -/
def frameEquiv : ((Fin k ⊕ Fin m) → K) ≃ₗ[K] ((Fin k ⊕ Fin m) → K) where
  toFun c := Sum.elim
    (fun r => y r * c (Sum.inl r))
    (fun i => c (Sum.inr i) + ∑ r, a i r * c (Sum.inl r))
  invFun t := Sum.elim
    (fun r => t (Sum.inl r) / y r)
    (fun i => t (Sum.inr i) - ∑ r, a i r * (t (Sum.inl r) / y r))
  left_inv c := by
    funext j
    cases j <;> simp [hy]
  right_inv t := by
    funext j
    cases j with
    | inl r => simp [div_eq_mul_inv, mul_comm, hy]
    | inr i => simp
  map_add' c d := by
    funext j
    cases j with
    | inl r => simp [mul_add]
    | inr i =>
      simp only [Pi.add_apply, Sum.elim_inr, mul_add, Finset.sum_add_distrib]
      abel
  map_smul' b c := by
    funext j
    cases j with
    | inl r => simp [mul_left_comm]
    | inr i => simp [Finset.mul_sum, mul_add, mul_left_comm]

/-- The logarithmic frame is a basis for any exponent matrix. -/
def frameBasis : Basis (Fin k ⊕ Fin m) K ((Fin k ⊕ Fin m) → K) :=
  (Pi.basisFun K _).map (frameEquiv a y hy)

@[simp] theorem frameBasis_repr_inl (t : (Fin k ⊕ Fin m) → K) (r : Fin k) :
    (frameBasis a y hy).repr t (Sum.inl r) = t (Sum.inl r) / y r := by
  change (Pi.basisFun K _).repr ((frameEquiv a y hy).symm t) (Sum.inl r) = _
  rw [Pi.basisFun_repr]
  rfl

@[simp] theorem frameBasis_repr_inr (t : (Fin k ⊕ Fin m) → K) (i : Fin m) :
    (frameBasis a y hy).repr t (Sum.inr i) =
      t (Sum.inr i) - ∑ r, a i r * (t (Sum.inl r) / y r) := by
  change (Pi.basisFun K _).repr ((frameEquiv a y hy).symm t) (Sum.inr i) = _
  rw [Pi.basisFun_repr]
  rfl

/-- Coordinate and logarithmic frames agree on every transverse column. -/
@[simp] theorem frameBasis_inr (i : Fin m) :
    frameBasis a y hy (Sum.inr i) = Pi.basisFun K _ (Sum.inr i) := by
  ext j
  cases j <;> simp [frameBasis, frameEquiv, Pi.basisFun_apply, Pi.single_apply]

@[simp] theorem frameBasis_inl_inl (r s : Fin k) :
    frameBasis a y hy (Sum.inl r) (Sum.inl s) = if s = r then y r else 0 := by
  by_cases hrs : s = r
  · subst s
    simp [frameBasis, frameEquiv, Pi.basisFun_apply]
  · simp [frameBasis, frameEquiv, Pi.basisFun_apply, Pi.single_apply, hrs]

@[simp] theorem frameBasis_inl_inr (r : Fin k) (i : Fin m) :
    frameBasis a y hy (Sum.inl r) (Sum.inr i) = a i r := by
  simp [frameBasis, frameEquiv, Pi.basisFun_apply, Pi.single_apply]

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- A transverse column mandatory in all normal bases forces the corresponding
logarithmic differential relation on the kernel of the normal quotient. -/
theorem mandatory_logarithmic_relation
    (q : ((Fin k ⊕ Fin m) → K) →ₗ[K] V) (hq : Function.Surjective q)
    (i : Fin m)
    (hi : ∀ B, IsNormalBasis (K := K) (fun j => q (frameBasis a y hy j)) B →
      Sum.inr i ∈ B)
    (t : (Fin k ⊕ Fin m) → K) (ht : q t = 0) :
    t (Sum.inr i) = ∑ r, a i r * (t (Sum.inl r) / y r) := by
  have h := mandatory_coordinate_eq_zero (frameBasis a y hy) q
    (span_mapped_basis_eq_top (frameBasis a y hy) q hq) (Sum.inr i) hi t ht
  rw [frameBasis_repr_inr] at h
  exact sub_eq_zero.mp h

/-- The entire set of transverse coordinates whose membership is forced by
normal-basis rigidity satisfies logarithmic differential relations. -/
theorem fixed_transverse_intersection_logarithmic_relations
    (q : ((Fin k ⊕ Fin m) → K) →ₗ[K] V) (hq : Function.Surjective q)
    (X I : Finset (Fin k ⊕ Fin m))
    (hfixed : ∀ B, IsNormalBasis (K := K) (fun j => q (frameBasis a y hy j)) B →
      B ∩ X = I)
    (i : Fin m) (hi : Sum.inr i ∈ I)
    (t : (Fin k ⊕ Fin m) → K) (ht : q t = 0) :
    t (Sum.inr i) = ∑ r, a i r * (t (Sum.inl r) / y r) := by
  apply mandatory_logarithmic_relation a y hy q hq i ?_ t ht
  intro B hB
  have hmem : Sum.inr i ∈ B ∩ X := by rw [hfixed B hB]; exact hi
  exact (Finset.mem_inter.mp hmem).1

/-- Use the canonical normal quotient by a tangent subspace. This formulation
can be applied directly to the coordinate vector of any derivation whose
coordinate vector belongs to `T`. -/
theorem tangent_subspace_logarithmic_relation
    (T : Submodule K ((Fin k ⊕ Fin m) → K))
    (i : Fin m)
    (hi : ∀ B, IsNormalBasis (K := K) (fun j => T.mkQ (frameBasis a y hy j)) B →
      Sum.inr i ∈ B)
    (t : (Fin k ⊕ Fin m) → K) (ht : t ∈ T) :
    t (Sum.inr i) = ∑ r, a i r * (t (Sum.inl r) / y r) := by
  apply mandatory_logarithmic_relation a y hy T.mkQ T.mkQ_surjective i hi t
  exact LinearMap.mem_ker.mp (by rwa [Submodule.ker_mkQ])

/-- Universal product comparison and directed transverse weight separation
force simultaneous logarithmic relations on the tangent subspace. The
multiplicity comparison and numerical separation remain explicit inputs. -/
theorem weighted_tangent_relations [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (T : Submodule K ((Fin k ⊕ Fin m) → K))
    (w cost : (Fin k ⊕ Fin m) → ℝ) (C : ℕ → ℝ)
    (hcomparison : ∀ A B,
      IsNormalBasis (K := K) (fun j => T.mkQ (Pi.basisFun K _ j)) A →
      IsNormalBasis (K := K) (fun j => T.mkQ (frameBasis a y hy j)) B →
      (∏ j ∈ A, w j) ≤ C A.card * ∏ j ∈ B, cost j)
    (hseparated : ∀ A B : Finset (Fin k ⊕ Fin m), A.card = B.card →
      ∀ i : Fin m, Sum.inr i ∈ A → Sum.inr i ∉ B →
      (∀ j : Fin m, frameOrder.lt (Sum.inr i) (Sum.inr j) →
        (Sum.inr j ∈ A ↔ Sum.inr j ∈ B)) →
      C A.card * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j) :
    ∃ I : Finset (Fin k ⊕ Fin m),
      IsGreedyBasis (K := K) (fun j => T.mkQ (Pi.basisFun K _ j))
        (Finset.univ.image Sum.inr) I ∧
      (∀ B, IsNormalBasis (K := K) (fun j => T.mkQ (frameBasis a y hy j)) B →
        B ∩ Finset.univ.image Sum.inr = I) ∧
      ∀ i : Fin m, Sum.inr i ∈ I → ∀ t ∈ T,
        t (Sum.inr i) = ∑ r, a i r * (t (Sum.inl r) / y r) := by
  classical
  let X : Finset (Fin k ⊕ Fin m) := Finset.univ.image Sum.inr
  have huv : ∀ j ∈ X, T.mkQ (Pi.basisFun K _ j) = T.mkQ (frameBasis a y hy j) := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    rw [frameBasis_inr]
  have hsep : ∀ A B : Finset (Fin k ⊕ Fin m), A.card = B.card →
      ∀ i, i ∈ X → i ∈ A → i ∉ B →
      (∀ j, j ∈ X → frameOrder.lt i j → (j ∈ A ↔ j ∈ B)) →
      C A.card * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j := by
    intro A B hcard i hi hiA hiB hlarge
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hi
    apply hseparated A B hcard i hiA hiB
    intro j hij
    exact hlarge (Sum.inr j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩) hij
  obtain ⟨I, hI, hfixed⟩ := weighted_normalBasis_transverse_rigidity
    (fun j => T.mkQ (Pi.basisFun K _ j)) (fun j => T.mkQ (frameBasis a y hy j)) X
    (span_mapped_basis_eq_top (Pi.basisFun K _) T.mkQ T.mkQ_surjective)
    huv w cost C hcomparison hsep
  have hfixed' : ∀ B, IsNormalBasis (K := K)
      (fun j => T.mkQ (frameBasis a y hy j)) B → B ∩ X = I := by
    intro B hB
    apply Finset.ext
    intro j
    have hj := Finset.ext_iff.mp (hfixed B hB) j
    simpa only [Finset.mem_inter] using hj
  refine ⟨I, hI, hfixed', ?_⟩
  intro i hi t ht
  apply fixed_transverse_intersection_logarithmic_relations a y hy T.mkQ
    T.mkQ_surjective X I hfixed' i hi t
  exact LinearMap.mem_ker.mp (by rwa [Submodule.ker_mkQ])

end MultivariateFrame

end

end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.MultivariateFrame.frameBasis_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateFrame.frameBasis_inr

/-- info: 'GeneralizedLogarithms.MultivariateFrame.mandatory_logarithmic_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateFrame.mandatory_logarithmic_relation

/-- info: 'GeneralizedLogarithms.MultivariateFrame.fixed_transverse_intersection_logarithmic_relations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateFrame.fixed_transverse_intersection_logarithmic_relations

/-- info: 'GeneralizedLogarithms.MultivariateFrame.weighted_tangent_relations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateFrame.weighted_tangent_relations
