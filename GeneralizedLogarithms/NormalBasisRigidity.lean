import LogIrrationalityMeasure.Jets.NormalBasisRigidity

/-!
# Rigidity of several transverse normal directions

The transverse directions form an arbitrary finite subset `X` of the ambient
index type.  The greatest independent subset in colexicographic order is the
descending greedy basis.  Unlike a comparison between bases of equal size,
its largest-discrepancy property applies to every independent subset of `X`.

The final theorem separates the finite-dimensional linear algebra from the
geometric multiplicity estimate: the universal product comparison and directed
weight separation are explicit hypotheses.
-/

namespace GeneralizedLogarithms

noncomputable section

open Set Submodule
open LogIrrationalityMeasure.LogExponent.NormalBasisRigidity

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The descending greedy independent set, specified as the greatest
independent subset in colexicographic order. -/
def IsGreedyBasis [LinearOrder ι] (v : ι → V) (X I : Finset ι) : Prop :=
  I ⊆ X ∧ LinearIndepOn K v (I : Set ι) ∧
    ∀ J : Finset ι, J ⊆ X → LinearIndepOn K v (J : Set ι) →
      toColex J ≤ toColex I

theorem exists_greedyBasis [LinearOrder ι] (v : ι → V) (X : Finset ι) :
    ∃ I, IsGreedyBasis (K := K) v X I := by
  classical
  let S : Finset (Finset ι) :=
    X.powerset.filter (fun I : Finset ι => LinearIndepOn K v (I : Set ι))
  have hS : S.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset,
      Finset.coe_empty, true_and]
    exact linearIndepOn_empty K v
  obtain ⟨I, hI, hmax⟩ := S.exists_max_image (fun J => toColex J) hS
  rcases Finset.mem_filter.mp hI with ⟨hIX, hli⟩
  refine ⟨I, Finset.mem_powerset.mp hIX, hli, ?_⟩
  intro J hJX hJ
  exact hmax J (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hJX, hJ⟩)

/-- A greedy independent set spans all transverse directions. -/
theorem IsGreedyBasis.span_eq [LinearOrder ι] {v : ι → V} {X I : Finset ι}
    (hI : IsGreedyBasis (K := K) v X I) :
    span K (v '' (I : Set ι)) = span K (v '' (X : Set ι)) := by
  classical
  apply le_antisymm
  · exact span_mono (Set.image_mono hI.1)
  · apply span_le.mpr
    rintro _ ⟨i, hiX, rfl⟩
    by_contra hi
    have hiI : i ∉ I := fun hiI => hi (subset_span ⟨i, hiI, rfl⟩)
    have hli : LinearIndepOn K v ((insert i I : Finset ι) : Set ι) := by
      simpa only [Finset.coe_insert] using hI.2.1.insert hi
    have hle := hI.2.2 (insert i I) (Finset.insert_subset_iff.mpr ⟨hiX, hI.1⟩) hli
    obtain ⟨j, hjI, hjnot, -⟩ :=
      (Finset.Colex.toColex_le_toColex.mp hle) (Finset.mem_insert_self i I) hiI
    exact hjnot (Finset.mem_insert_of_mem hjI)

/-- The largest discrepancy with any other independent subset lies in the
greedy set.  No equality of cardinalities is assumed. -/
theorem IsGreedyBasis.largest_discrepancy [LinearOrder ι]
    {v : ι → V} {X I : Finset ι} (hI : IsGreedyBasis (K := K) v X I)
    (J : Finset ι) (hJX : J ⊆ X) (hJ : LinearIndepOn K v (J : Set ι))
    (hJI : J ≠ I) :
    ∃ i, i ∈ I ∧ i ∉ J ∧ ∀ j, i < j → (j ∈ I ↔ j ∈ J) := by
  classical
  have hlt : toColex J < toColex I :=
    lt_of_le_of_ne (hI.2.2 J hJX hJ) (fun h => hJI (toColex.injective h))
  obtain ⟨i, hi, hfilters⟩ := Finset.Colex.lt_iff_exists_filter_lt.mp hlt
  refine ⟨i, (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2, ?_⟩
  intro j hij
  have hmem := Finset.ext_iff.mp hfilters j
  simpa only [Finset.mem_filter, hij, and_true] using hmem.symm

/-- Extend a transverse basis to an ambient normal basis without adding any
further transverse index.  All new directions lie outside `X`. -/
theorem exists_normalBasis_with_intersection [Fintype ι] [DecidableEq ι]
    (v : ι → V) (hv : span K (Set.range v) = ⊤) (X I : Finset ι)
    (hIX : I ⊆ X) (hli : LinearIndepOn K v (I : Set ι))
    (hspan : span K (v '' (I : Set ι)) = span K (v '' (X : Set ι))) :
    ∃ A, IsNormalBasis (K := K) v A ∧ A ∩ X = I := by
  classical
  let A := hli.extend (Set.subset_univ (I : Set ι))
  have hIA : (I : Set ι) ⊆ A := hli.subset_extend (Set.subset_univ _)
  have hAli : LinearIndepOn K v A := hli.linearIndepOn_extend (Set.subset_univ _)
  have hAnormal : IsNormalBasis (K := K) v A.toFinset := by
    constructor
    · simpa only [Set.coe_toFinset] using hAli
    · simpa only [A, Set.coe_toFinset, Set.image_univ] using
        (hli.span_image_extend_eq_span_image (Set.subset_univ _)).trans
          (by simpa only [Set.image_univ] using hv)
  refine ⟨A.toFinset, hAnormal, ?_⟩
  apply Finset.ext
  intro i
  constructor
  · intro hi
    rcases Finset.mem_inter.mp hi with ⟨hiA, hiX⟩
    by_contra hiI
    have himem : v i ∈ span K (v '' (I : Set ι)) := by
      rw [hspan]
      exact subset_span ⟨i, hiX, rfl⟩
    apply hAli.notMem_span (Set.mem_toFinset.mp hiA)
    apply span_mono (Set.image_mono ?_) himem
    intro j hj
    exact ⟨hIA hj, fun hji => hiI (hji ▸ hj)⟩
  · intro hi
    exact Finset.mem_inter.mpr ⟨Set.mem_toFinset.mpr (hIA hi), hIX hi⟩

/-- Universal coordinate/frame product comparison, together with directed
transverse separation, fixes the entire transverse part of every frame basis.

The separation hypothesis only concerns a transverse discrepancy.  It imposes
no condition on pairs that differ solely in longitudinal indices. -/
theorem weighted_normalBasis_transverse_rigidity [Fintype ι] [LinearOrder ι]
    (u v : ι → V) (X : Finset ι) (hu : span K (Set.range u) = ⊤)
    (huv : ∀ i ∈ X, u i = v i)
    (w cost : ι → ℝ) (C : ℕ → ℝ)
    (hcomparison : ∀ A B, IsNormalBasis (K := K) u A →
      IsNormalBasis (K := K) v B →
      (∏ j ∈ A, w j) ≤ C A.card * ∏ j ∈ B, cost j)
    (hseparated : ∀ A B : Finset ι, A.card = B.card →
      ∀ i, i ∈ X → i ∈ A → i ∉ B →
      (∀ j, j ∈ X → i < j → (j ∈ A ↔ j ∈ B)) →
      C A.card * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j) :
    ∃ I, IsGreedyBasis (K := K) u X I ∧
      ∀ B, IsNormalBasis (K := K) v B → B ∩ X = I := by
  classical
  obtain ⟨I, hI⟩ := exists_greedyBasis (K := K) u X
  obtain ⟨A, hA, hAX⟩ := exists_normalBasis_with_intersection u hu X I
    hI.1 hI.2.1 hI.span_eq
  refine ⟨I, hI, ?_⟩
  intro B hB
  by_contra hBX
  have hJ : LinearIndepOn K u ((B ∩ X : Finset ι) : Set ι) := by
    apply (hB.1.mono (by intro j hj; exact (Finset.mem_inter.mp hj).1)).congr
    intro j hj
    exact (huv j (Finset.mem_inter.mp hj).2).symm
  obtain ⟨i, hiI, hiBX, hlarge⟩ :=
    hI.largest_discrepancy (B ∩ X) Finset.inter_subset_right hJ hBX
  have hiX : i ∈ X := hI.1 hiI
  have hiA : i ∈ A := (Finset.mem_inter.mp (hAX.symm ▸ hiI)).1
  have hiB : i ∉ B := fun hiB => hiBX (Finset.mem_inter.mpr ⟨hiB, hiX⟩)
  have hlarge' : ∀ j, j ∈ X → i < j → (j ∈ A ↔ j ∈ B) := by
    intro j hjX hij
    have hj := hlarge j hij
    rw [← hAX] at hj
    simpa only [Finset.mem_inter, hjX, and_true] using hj
  exact (not_lt_of_ge (hcomparison A B hA hB))
    (hseparated A B (hA.card_eq.trans hB.card_eq.symm) i hiX hiA hiB hlarge')

end

end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.exists_greedyBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.exists_greedyBasis

/-- info: 'GeneralizedLogarithms.IsGreedyBasis.largest_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.IsGreedyBasis.largest_discrepancy

/-- info: 'GeneralizedLogarithms.weighted_normalBasis_transverse_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.weighted_normalBasis_transverse_rigidity
