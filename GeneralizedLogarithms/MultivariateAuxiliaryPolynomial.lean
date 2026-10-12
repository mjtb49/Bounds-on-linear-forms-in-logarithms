import GeneralizedLogarithms.MultivariateFormalJet
import LogIrrationalityMeasure.Polynomials.AuxiliaryPolynomial
import LogIrrationalityMeasure.Approximation.WeightedSliceDegree

/-!
# Auxiliary polynomials for multilogarithmic jets

The original weighted-simplex count applies in dimension `k + m`. Reindexing
its polynomial coefficient space gives a nonzero polynomial in the actual
longitudinal and transverse variables that kills every requested low jet.
The eventual degree threshold is uniform in the integer matrix and centers.
-/

namespace GeneralizedLogarithms.MultivariateAuxiliaryPolynomial

noncomputable section

open scoped BigOperators
open Filter Topology
open LogIrrationalityMeasure.LogExponent
open MultivariatePolynomialFrame MultivariateFormalJet

variable {k m : ℕ} {J : Type*} [Fintype J]

/-- The finite coordinate reindexing used only for the existing simplex count. -/
def indexEquiv : Fin (k + m) ≃ (Fin k ⊕ Fin m) := finSumFinEquiv.symm

def simplexExponent (d : Fin (k + m) → ℕ) : (Fin k ⊕ Fin m) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => d (indexEquiv.symm j))

@[simp] theorem simplexExponent_apply (d : Fin (k + m) → ℕ) (j : Fin k ⊕ Fin m) :
    simplexExponent d j = d (indexEquiv.symm j) := rfl

theorem polynomialOfCoefficients_supportBound {d : ℕ} (W : Fin d → ℝ)
    (hW : ∀ i, 0 < W i) (N : ℝ) (x : ↥(realWeightedSimplex W N) → ℂ) :
    WeightedSliceDegree.SupportBound W N
      (polynomialOfCoefficients (realWeightedSimplex W N) x) := by
  classical
  intro e he
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (polynomialOfCoefficients_support _ x he)
  have h := (mem_realWeightedSimplex hW).mp hb
  simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul,
    InterpolationMatrix.exponentVector_apply, mul_comm] using h

theorem supportBound_renameEquiv {ι τ : Type*} (e : ι ≃ τ)
    (W : τ → ℝ) (N : ℝ) (p : MvPolynomial ι ℂ)
    (hp : WeightedSliceDegree.SupportBound (fun i => W (e i)) N p) :
    WeightedSliceDegree.SupportBound W N (MvPolynomial.renameEquiv ℂ e p) := by
  change WeightedSliceDegree.SupportBound W N (MvPolynomial.rename e p)
  rw [MvPolynomial.rename_eq_aeval]
  exact WeightedSliceDegree.supportBound_aeval (fun i => W (e i)) W
    (MvPolynomial.X ∘ e) (fun i => WeightedSliceDegree.supportBound_X W (e i)) N p hp

/-- Dimension counting kills any linear family of the indicated size. The map
may depend arbitrarily on the degree, coefficient matrix, and centers. -/
theorem eventually_exists_auxiliaryPolynomial
    (W V : (Fin k ⊕ Fin m) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    {scale : ℝ} (hscale : 0 < scale)
    (hvol : (Fintype.card J : ℝ) * scale ^ (k + m) *
      (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1) :
    ∀ᶠ N : ℝ in atTop,
      ∀ E : Polynomial ℂ k m →ₗ[ℂ]
        ((J × ↥(strictWeightedSimplex
          (fun i : Fin (k + m) => (V (indexEquiv i) : ℝ)) (scale * N))) → ℂ),
      ∃ p : Polynomial ℂ k m, p ≠ 0 ∧
        WeightedSliceDegree.SupportBound (fun i => (W i : ℝ)) N p ∧ E p = 0 := by
  classical
  let e : Fin (k + m) ≃ (Fin k ⊕ Fin m) := indexEquiv
  have hvol' : (Fintype.card J : ℝ) * scale ^ (k + m) *
      (∏ i, (W (e i) : ℝ)) / (∏ i, (V (e i) : ℝ)) < 1 := by
    rw [e.prod_comp (fun i => (W i : ℝ)), e.prod_comp (fun i => (V i : ℝ))]
    exact hvol
  filter_upwards [eventually_auxiliary_card_lt (fun i => W (e i))
    (fun i => V (e i)) (fun i => hW (e i)) (fun i => hV (e i))
    (Fintype.card J) hscale hvol'] with N hN
  intro E
  let S := realWeightedSimplex (fun i => (W (e i) : ℝ)) N
  let A := E.comp ((MvPolynomial.renameEquiv ℂ e).toLinearMap.comp
    (polynomialOfCoefficients S))
  have hcard : Fintype.card (J × ↥(strictWeightedSimplex
      (fun i : Fin (k + m) => (V (e i) : ℝ)) (scale * N))) < Fintype.card S := by
    simpa [S] using hN
  obtain ⟨x, hx, hAx⟩ := exists_nonzero_kernel_of_card_lt A hcard
  refine ⟨MvPolynomial.renameEquiv ℂ e (polynomialOfCoefficients S x), ?_, ?_, hAx⟩
  · intro hp
    apply hx
    apply polynomialOfCoefficients_injective S
    apply (MvPolynomial.renameEquiv ℂ e).injective
    simpa using hp
  · exact supportBound_renameEquiv e (fun i => (W i : ℝ)) N _
      (polynomialOfCoefficients_supportBound (fun i => (W (e i) : ℝ))
        (fun i => by exact_mod_cast hW (e i)) N x)

/-- The finite collection of low coefficients of the actual formal jets. -/
def formalJetEvaluation (a : Fin m → Fin k → ℤ)
    (V : (Fin k ⊕ Fin m) → ℝ) (H : ℝ) (c : J → (Fin k ⊕ Fin m) → ℂ) :
    Polynomial ℂ k m →ₗ[ℂ]
      ((J × ↥(strictWeightedSimplex (fun i => V (indexEquiv i)) H)) → ℂ) :=
  LinearMap.pi (fun ρ => (MvPowerSeries.coeff (simplexExponent ρ.2.val)).comp
    (formalJet a (c ρ.1)).toLinearMap)

/-- The large-degree threshold depends only on weights, scale and the number
of centers, uniformly over all integer matrices and center coordinates. -/
theorem eventually_exists_formalJet_auxiliaryPolynomial_uniform
    (W V : (Fin k ⊕ Fin m) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    {scale : ℝ} (hscale : 0 < scale)
    (hvol : (Fintype.card J : ℝ) * scale ^ (k + m) *
      (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1) :
    ∀ᶠ N : ℝ in atTop, ∀ a : Fin m → Fin k → ℤ,
      ∀ c : J → (Fin k ⊕ Fin m) → ℂ,
      ∃ p : Polynomial ℂ k m, p ≠ 0 ∧
        WeightedSliceDegree.SupportBound (fun i => (W i : ℝ)) N p ∧
        ∀ j d, Finsupp.weight (fun i => (V i : ℝ)) d < scale * N →
          MvPowerSeries.coeff d (formalJet a (c j) p) = 0 := by
  filter_upwards [eventually_exists_auxiliaryPolynomial W V hW hV hscale hvol] with N hN
  intro a c
  obtain ⟨p, hp, hdegree, he⟩ :=
    hN (formalJetEvaluation a (fun i => (V i : ℝ)) (scale * N) c)
  refine ⟨p, hp, hdegree, ?_⟩
  intro j d hd
  have hsum : (∑ i : Fin (k + m), (V (indexEquiv i) : ℝ) * (d (indexEquiv i) : ℝ)) =
      Finsupp.weight (fun i => (V i : ℝ)) d := by
    rw [Finsupp.weight_eq_sum]
    simpa only [nsmul_eq_mul, mul_comm] using
      indexEquiv.sum_comp (fun i : Fin k ⊕ Fin m => (V i : ℝ) * (d i : ℝ))
  have hmem : (fun i : Fin (k + m) => d (indexEquiv i)) ∈
      strictWeightedSimplex (fun i => (V (indexEquiv i) : ℝ)) (scale * N) := by
    apply (mem_strictWeightedSimplex (fun i => by exact_mod_cast hV (indexEquiv i))).mpr
    rwa [hsum]
  have hh := congrFun he (j, ⟨(fun i => d (indexEquiv i)), hmem⟩)
  have hexp : simplexExponent (fun i => d (indexEquiv i)) = d := by
    ext i
    simp only [simplexExponent_apply, Equiv.apply_symm_apply]
  simpa only [formalJetEvaluation, LinearMap.pi_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, hexp, Pi.zero_apply] using hh

/-- Natural degrees and rational jet bounds, still uniform in all matrices
and centers. -/
theorem eventually_exists_formalJet_auxiliaryPolynomial_nat_uniform
    (W V : (Fin k ⊕ Fin m) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    {scale : ℚ} (hscale : 0 < scale)
    (hvol : (Fintype.card J : ℝ) * (scale : ℝ) ^ (k + m) *
      (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ a : Fin m → Fin k → ℤ,
      ∀ c : J → (Fin k ⊕ Fin m) → ℂ,
      ∃ p : Polynomial ℂ k m, p ≠ 0 ∧
        WeightedSliceDegree.SupportBound (fun i => (W i : ℝ)) (N : ℝ) p ∧
        ∀ j, formalJet a (c j) p ∈
          JetGeometry.rationalWeightedIdeal V (fun i => (hV i).le) (scale * N) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_exists_formalJet_auxiliaryPolynomial_uniform W V hW hV
      (by exact_mod_cast hscale) hvol)
  filter_upwards [h] with N hN
  intro a c
  obtain ⟨p, hp, hdegree, hcoeff⟩ := hN a c
  refine ⟨p, hp, hdegree, ?_⟩
  intro j d hd
  apply hcoeff j d
  have hcast : ((Finsupp.weight V d : ℚ) : ℝ) < (scale : ℝ) * (N : ℝ) := by
    exact_mod_cast hd
  simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_natCast] using hcast

/-- Fixed-matrix, fixed-center form for direct use in the curve argument. -/
theorem eventually_exists_formalJet_auxiliaryPolynomial_nat
    (a : Fin m → Fin k → ℤ)
    (W V : (Fin k ⊕ Fin m) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    {scale : ℚ} (hscale : 0 < scale)
    (hvol : (Fintype.card J : ℝ) * (scale : ℝ) ^ (k + m) *
      (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (c : J → (Fin k ⊕ Fin m) → ℂ) :
    ∀ᶠ N : ℕ in atTop, ∃ p : Polynomial ℂ k m, p ≠ 0 ∧
      WeightedSliceDegree.SupportBound (fun i => (W i : ℝ)) (N : ℝ) p ∧
      ∀ j, formalJet a (c j) p ∈
        JetGeometry.rationalWeightedIdeal V (fun i => (hV i).le) (scale * N) := by
  filter_upwards [eventually_exists_formalJet_auxiliaryPolynomial_nat_uniform
    W V hW hV hscale hvol] with N hN
  exact hN a c

end
end GeneralizedLogarithms.MultivariateAuxiliaryPolynomial

/-- info: 'GeneralizedLogarithms.MultivariateAuxiliaryPolynomial.eventually_exists_auxiliaryPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAuxiliaryPolynomial.eventually_exists_auxiliaryPolynomial

/-- info: 'GeneralizedLogarithms.MultivariateAuxiliaryPolynomial.eventually_exists_formalJet_auxiliaryPolynomial_nat_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAuxiliaryPolynomial.eventually_exists_formalJet_auxiliaryPolynomial_nat_uniform

/-- info: 'GeneralizedLogarithms.MultivariateAuxiliaryPolynomial.eventually_exists_formalJet_auxiliaryPolynomial_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAuxiliaryPolynomial.eventually_exists_formalJet_auxiliaryPolynomial_nat
