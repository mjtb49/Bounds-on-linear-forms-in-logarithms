import LogIrrationalityMeasure.LocalAlgebra.WeightedBezout

/-!
# Polynomial coordinates for multivariate compact jet ideals

Triangular coordinates with several longitudinal variables are polynomial
automorphisms. Their positive coordinate-power ideals are supported at the
specified center. The transverse correction polynomials are arbitrary
polynomials in the longitudinal variables, so sums of truncated logarithms
can be inserted without another automorphism argument.
-/

namespace GeneralizedLogarithms.MultivariateCompactJetPolynomial

noncomputable section

open MvPolynomial
open LogIrrationalityMeasure.LogExponent
open scoped BigOperators

variable {R ι κ : Type*} [Field R]

def centeredY (c : ι ⊕ κ → R) (r : ι) : MvPolynomial (ι ⊕ κ) R :=
  C (c (Sum.inl r))⁻¹ * X (Sum.inl r) - 1

def triangularMap (c : ι ⊕ κ → R) (G : κ → MvPolynomial ι R) :
    MvPolynomial (ι ⊕ κ) R →ₐ[R] MvPolynomial (ι ⊕ κ) R :=
  aeval (Sum.elim (fun r => C (c (Sum.inl r)) * (1 + X (Sum.inl r)))
    (fun i => C (c (Sum.inr i)) + X (Sum.inr i) +
      aeval (fun r => X (Sum.inl r)) (G i)))

def coordinates (c : ι ⊕ κ → R) (G : κ → MvPolynomial ι R) :
    ι ⊕ κ → MvPolynomial (ι ⊕ κ) R :=
  Sum.elim (centeredY c)
    (fun i => X (Sum.inr i) - C (c (Sum.inr i)) - aeval (centeredY c) (G i))

def inverseTriangularMap (c : ι ⊕ κ → R) (G : κ → MvPolynomial ι R) :
    MvPolynomial (ι ⊕ κ) R →ₐ[R] MvPolynomial (ι ⊕ κ) R := aeval (coordinates c G)

@[simp] theorem triangularMap_X_inl (c : ι ⊕ κ → R) (G : κ → MvPolynomial ι R) (r : ι) :
    triangularMap c G (X (Sum.inl r)) = C (c (Sum.inl r)) * (1 + X (Sum.inl r)) := by
  simp [triangularMap]

@[simp] theorem triangularMap_X_inr (c : ι ⊕ κ → R) (G : κ → MvPolynomial ι R) (i : κ) :
    triangularMap c G (X (Sum.inr i)) = C (c (Sum.inr i)) + X (Sum.inr i) +
      aeval (fun r => X (Sum.inl r)) (G i) := by simp [triangularMap]

@[simp] theorem inverseTriangularMap_X (c : ι ⊕ κ → R) (G : κ → MvPolynomial ι R)
    (j : ι ⊕ κ) : inverseTriangularMap c G (X j) = coordinates c G j := by
  simp [inverseTriangularMap]

@[simp] theorem triangularMap_centeredY (c : ι ⊕ κ → R)
    (hc : ∀ r, c (Sum.inl r) ≠ 0) (G : κ → MvPolynomial ι R) (r : ι) :
    triangularMap c G (centeredY c r) = X (Sum.inl r) := by
  have h : (C (c (Sum.inl r))⁻¹ : MvPolynomial (ι ⊕ κ) R) * C (c (Sum.inl r)) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (hc r), map_one]
  simp only [centeredY, map_sub, map_mul, map_one, MvPolynomial.algHom_C,
    triangularMap_X_inl, MvPolynomial.algebraMap_eq]
  rw [← mul_assoc, h, one_mul]
  ring

@[simp] theorem inverseTriangularMap_longitudinal_image (c : ι ⊕ κ → R)
    (hc : ∀ r, c (Sum.inl r) ≠ 0) (G : κ → MvPolynomial ι R) (r : ι) :
    inverseTriangularMap c G (C (c (Sum.inl r)) * (1 + X (Sum.inl r))) = X (Sum.inl r) := by
  have h : (C (c (Sum.inl r)) : MvPolynomial (ι ⊕ κ) R) * C (c (Sum.inl r))⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (hc r), map_one]
  simp only [map_mul, map_add, map_one, MvPolynomial.algHom_C,
    inverseTriangularMap_X, coordinates, Sum.elim_inl, centeredY, MvPolynomial.algebraMap_eq]
  rw [show (1 : MvPolynomial (ι ⊕ κ) R) +
      (C (c (Sum.inl r))⁻¹ * X (Sum.inl r) - 1) =
      C (c (Sum.inl r))⁻¹ * X (Sum.inl r) by ring, ← mul_assoc, h, one_mul]

theorem triangularMap_comp_inverse (c : ι ⊕ κ → R)
    (hc : ∀ r, c (Sum.inl r) ≠ 0) (G : κ → MvPolynomial ι R) :
    (triangularMap c G).comp (inverseTriangularMap c G) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro j
  cases j with
  | inl r => simp [coordinates, triangularMap_centeredY c hc G]
  | inr i =>
    simp only [AlgHom.comp_apply, inverseTriangularMap_X, coordinates, Sum.elim_inr,
      map_sub, triangularMap_X_inr, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
      MvPolynomial.comp_aeval_apply, triangularMap_centeredY c hc G, AlgHom.id_apply]
    ring

theorem inverseTriangularMap_comp (c : ι ⊕ κ → R)
    (hc : ∀ r, c (Sum.inl r) ≠ 0) (G : κ → MvPolynomial ι R) :
    (inverseTriangularMap c G).comp (triangularMap c G) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro j
  cases j with
  | inl r => simp [inverseTriangularMap_longitudinal_image c hc G]
  | inr i =>
    simp only [AlgHom.comp_apply, triangularMap_X_inr, map_add,
      inverseTriangularMap_X, coordinates, Sum.elim_inr, Sum.elim_inl,
      MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, MvPolynomial.comp_aeval_apply,
      AlgHom.id_apply]
    ring

def triangularEquiv (c : ι ⊕ κ → R) (hc : ∀ r, c (Sum.inl r) ≠ 0)
    (G : κ → MvPolynomial ι R) :
    MvPolynomial (ι ⊕ κ) R ≃ₐ[R] MvPolynomial (ι ⊕ κ) R :=
  AlgEquiv.ofAlgHom (triangularMap c G) (inverseTriangularMap c G)
    (triangularMap_comp_inverse c hc G) (inverseTriangularMap_comp c hc G)

@[simp] theorem aeval_centeredY (c : ι ⊕ κ → R) (hc : ∀ r, c (Sum.inl r) ≠ 0) (r : ι) :
    aeval c (centeredY c r) = 0 := by simp [centeredY, inv_mul_cancel₀ (hc r)]

theorem eval_center_inverse (c : ι ⊕ κ → R) (hc : ∀ r, c (Sum.inl r) ≠ 0)
    (G : κ → MvPolynomial ι R) (hG : ∀ i, aeval (0 : ι → R) (G i) = 0) :
    (aeval c).comp (inverseTriangularMap c G) = aeval (0 : ι ⊕ κ → R) := by
  apply MvPolynomial.algHom_ext
  intro j
  cases j with
  | inl r =>
    simpa only [AlgHom.comp_apply, inverseTriangularMap_X, coordinates,
      Sum.elim_inl, aeval_X, Pi.zero_apply] using aeval_centeredY c hc r
  | inr i =>
    simp only [AlgHom.comp_apply, inverseTriangularMap_X, coordinates, Sum.elim_inr,
      map_sub, aeval_X, aeval_C, MvPolynomial.comp_aeval_apply, aeval_centeredY c hc]
    change c (Sum.inr i) - c (Sum.inr i) - aeval (0 : ι → R) (G i) = 0
    rw [hG i]
    ring

def powerIdeal (c : ι ⊕ κ → R) (G : κ → MvPolynomial ι R) (e : ι ⊕ κ → ℕ) :
    Ideal (MvPolynomial (ι ⊕ κ) R) :=
  Ideal.span (Set.range (fun j => coordinates c G j ^ e j))

theorem span_coordinates (c : ι ⊕ κ → R) (hc : ∀ r, c (Sum.inl r) ≠ 0)
    (G : κ → MvPolynomial ι R) (hG : ∀ i, aeval (0 : ι → R) (G i) = 0) :
    Ideal.span (Set.range (coordinates c G)) = WeightedBezout.pointIdeal c := by
  let φ := (inverseTriangularMap c G).toRingHom
  have hs : Function.Surjective φ := (triangularEquiv c hc G).symm.surjective
  have hcm : (WeightedBezout.pointIdeal c).comap φ =
      WeightedBezout.pointIdeal (0 : ι ⊕ κ → R) := by
    ext P
    change aeval c (inverseTriangularMap c G P) = 0 ↔ aeval (0 : ι ⊕ κ → R) P = 0
    rw [← AlgHom.comp_apply, eval_center_inverse c hc G hG]
  calc
    _ = (Ideal.span (Set.range (X (R := R) : ι ⊕ κ → _))).map φ := by
      rw [Ideal.map_span, ← Set.range_comp]
      simp only [Function.comp_def, inverseTriangularMap_X, φ, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
    _ = (WeightedBezout.pointIdeal (0 : ι ⊕ κ → R)).map φ := by
      congr 1
      rw [WeightedBezout.pointIdeal_eq_span]
      simp
    _ = WeightedBezout.pointIdeal c := by rw [← hcm, Ideal.map_comap_of_surjective φ hs]

theorem radical_powerIdeal (c : ι ⊕ κ → R) (hc : ∀ r, c (Sum.inl r) ≠ 0)
    (G : κ → MvPolynomial ι R) (hG : ∀ i, aeval (0 : ι → R) (G i) = 0)
    (e : ι ⊕ κ → ℕ) (he : ∀ j, 0 < e j) :
    (powerIdeal c G e).radical = WeightedBezout.pointIdeal c := by
  apply le_antisymm
  · apply (Ideal.IsPrime.radical_le_iff
      (inferInstance : (WeightedBezout.pointIdeal c).IsPrime)).mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hz : coordinates c G j ∈ WeightedBezout.pointIdeal c := by
      rw [← span_coordinates c hc G hG]
      exact Ideal.subset_span ⟨j, rfl⟩
    change aeval c (coordinates c G j ^ e j) = 0
    rw [map_pow, (WeightedBezout.mem_pointIdeal _ _).mp hz, zero_pow (he j).ne']
  · rw [← span_coordinates c hc G hG]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨e j, Ideal.subset_span ⟨j, rfl⟩⟩

def centerPoint (c : ι ⊕ κ → R) : PrimeSpectrum (MvPolynomial (ι ⊕ κ) R) :=
  ⟨WeightedBezout.pointIdeal c, inferInstance⟩

theorem zeroLocus_powerIdeal (c : ι ⊕ κ → R) (hc : ∀ r, c (Sum.inl r) ≠ 0)
    (G : κ → MvPolynomial ι R) (hG : ∀ i, aeval (0 : ι → R) (G i) = 0)
    (e : ι ⊕ κ → ℕ) (he : ∀ j, 0 < e j) :
    PrimeSpectrum.zeroLocus (powerIdeal c G e : Set _) = {centerPoint c} := by
  rw [← PrimeSpectrum.zeroLocus_radical, radical_powerIdeal c hc G hG e he]
  exact PrimeSpectrum.zeroLocus_eq_singleton _

end
end GeneralizedLogarithms.MultivariateCompactJetPolynomial

/-- info: 'GeneralizedLogarithms.MultivariateCompactJetPolynomial.triangularEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCompactJetPolynomial.triangularEquiv

/-- info: 'GeneralizedLogarithms.MultivariateCompactJetPolynomial.radical_powerIdeal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCompactJetPolynomial.radical_powerIdeal

/-- info: 'GeneralizedLogarithms.MultivariateCompactJetPolynomial.zeroLocus_powerIdeal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCompactJetPolynomial.zeroLocus_powerIdeal
