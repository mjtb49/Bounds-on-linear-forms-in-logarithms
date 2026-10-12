import GeneralizedLogarithms.MultivariateMatrixBounds
import GeneralizedLogarithms.MultivariateDeterminantLimit

/-! The arithmetic and analytic estimates contradict one another on the
nonzero minors supplied by geometric interpolation. -/

namespace GeneralizedLogarithms.MultivariateDeterminantContradiction

noncomputable section
open scoped BigOperators Topology
open Filter LogIrrationalityMeasure.LogExponent
open MultivariateAnalyticSetup MultivariateMatrixBounds MultivariateModeCapacity
open MultivariateArithmetic MultivariateArithmeticBounds MultivariateDeterminantLimit

variable {k m K : ℕ} [LinearOrder (Fin k ⊕ Fin m)]

/-- Explicit numerical and approximation data are impossible when the
arithmetic cost is below the analytic decay. All geometric interpolation,
integrality, Taylor expansion, collision and limiting steps are discharged. -/
theorem impossible (hk : 0 < k) (hK : 0 < K)
    (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ)
    (G : MultivariateCurveMargin.NumericalData a (fun j : Fin K => center α p j.val))
    (D : Data α a p K) (v₀ θ : ℚ) (w : Fin m → ℚ)
    (hv : 0 < v₀) (hθ : 0 < θ) (hw : ∀ i, 0 < w i)
    (hDw : D.w = fun i => (w i : ℝ)) (hDv : D.v₀ = v₀) (hDt : D.θ = θ)
    (hGw : (fun s => (G.w s : ℝ)) = degreeWeights D.w₀ D.w)
    (hGv : G.v = jetWeights v₀ θ w)
    (hT : ∀ i r, G.v (Sum.inr i) ≤ (D.T i : ℚ)*G.v (Sum.inl r))
    (hA : 0 < D.A) (hS : 0 < D.S)
    (hcapacity : capacityDensity (k := k) w D.A D.S < D.η*rowDensity (k := k) K v₀ θ w/2)
    (hcost : cost α D.T (K-1) (degreeWeights D.w₀ D.w) < D.c) : False := by
  obtain ⟨R, hR, hgeom⟩ := eventual_minor_with_arithmetic_bound hk α a p K hK G D.T hT
  rw [hGw, hGv] at hgeom
  have hheight : Tendsto (fun n : ℕ => (((n : ℚ)*(R : ℚ) : ℚ) : ℝ)) atTop atTop := by
    have hh : Tendsto (fun n : ℕ => (R : ℝ)*(n : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by exact_mod_cast hR) tendsto_natCast_atTop_atTop
    simpa only [Rat.cast_mul, Rat.cast_natCast, mul_comm] using hh
  have hcap := hheight.eventually (eventually_capacity_le K v₀ θ w hv hθ hw
    D.A D.S D.η hA hS hcapacity)
  have hlim := tendsto_overhead k m K hK v₀ θ w hv hθ hw
  have hsmall := hheight.eventually (hlim.eventually
    (gt_mem_nhds (sub_pos.mpr hcost)))
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hgeom,hcap,hsmall,eventually_ge_atTop (1 : ℕ)] with n hn hcapn hsmalln hnpos
    obtain ⟨selection,hne,hlower⟩ := hn
    let H : ℚ := (n : ℚ)*R
    have hH : 0 < H := mul_pos (by exact_mod_cast (show 0<n by omega)) (by exact_mod_cast hR)
    have hupper := norm_minor_le hk α a p D v₀ θ w hv hθ hw hDw hDv hDt H hH.le selection hcapn
    have hM := row_card_pos (k := k) K hK (jetWeights v₀ θ w) (jetWeights_pos v₀ θ w hv hθ hw) H hH
    have hlog := normalized_log_upper D.v₀ (H : ℝ) D.c _ hM (by exact_mod_cast hH)
      (norm_pos_iff.mpr hne) hupper
    rw [hDv, row_card_eq] at hlog
    have hlower' := hlower
    rw [row_card_eq] at hlower'
    change overhead k m v₀ (rowCount (k := k) K v₀ θ w H) H <
      D.c-cost α D.T (K-1) (degreeWeights D.w₀ D.w) at hsmalln
    linarith
  exact (Filter.Eventually.exists hfalse).choose_spec

end
end GeneralizedLogarithms.MultivariateDeterminantContradiction

/-- info: 'GeneralizedLogarithms.MultivariateDeterminantContradiction.impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateDeterminantContradiction.impossible
