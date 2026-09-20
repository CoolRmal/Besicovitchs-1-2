/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Besicovitch.Main.Bound
public import Besicovitch.SixPoint.GramWeightedBound
public import Besicovitch.Measure.HausdorffSeparable
public import Besicovitch.Rectifiability.Isometry

/-!
# The rational bound in every real inner product space

The Gram certificates give the weighted geometric bound at the small rational weights, the finite
failure tree turns that into the six-point finite property at `barS = 6934/10000`, and the
six-point transfer turns that into the Besicovitch pair condition and the rectifiability bound.
The pair condition holds in every real inner product space. The bound on `sigmaOne` holds in
every complete real inner product space, without a separability assumption: each finite-length
set lies in a separable closed linear subspace. The planar statements are the instances at
`EuclideanSpace ℝ (Fin 2)`.
-/

@[expose] public section

noncomputable section

namespace Besicovitch

section InnerProductSpace

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The six-point finite property holds at `barS` in every real inner product space. -/
theorem sixPointFiniteProperty_barS : SixPointFiniteProperty E barS :=
  sixPointFiniteProperty_barS_of_weightedGeometricBound gramLambda_pos gramMu_pos
    weightedGeometricBound_gram

variable [MeasurableSpace E] [BorelSpace E]

/-- Every density parameter above `6934 / 10000` satisfies the Besicovitch pair condition in a
real inner product space. -/
theorem besicovitchPairCondition_of_gt {β : ℝ} (hβ : 6934 / 10000 < β) :
    BesicovitchPairCondition E β :=
  (sixPointFiniteProperty_barS E).besicovitchPairCondition barS_pos (by rwa [barS_eq])

variable [CompleteSpace E]

/-- Every threshold above `6934 / 10000` forces one-rectifiability in a real Hilbert space,
without any separability assumption. -/
theorem forcesOneRectifiability_of_gt {β : ℝ} (hβ : 6934 / 10000 < β) :
    ForcesOneRectifiability E (ENNReal.ofReal β) := by
  intro s hs hfinite hdensity
  let K := (Submodule.span ℝ s).topologicalClosure
  have hsep : TopologicalSpace.IsSeparable (K : Set E) :=
    (isSeparable_of_hausdorffMeasure_lt_top hfinite).span.closure
  letI : TopologicalSpace.SeparableSpace K := hsep.separableSpace
  have hforce : ForcesOneRectifiability K (ENNReal.ofReal β) :=
    (sixPointFiniteProperty_barS K).forcesOneRectifiability_of_gt barS_pos barS_lt_one
      (by rwa [barS_eq])
  apply rectifiable_of_forcesOneRectifiability_of_isometry
    (isometry_subtype_coe (s := (K : Set E))) hforce hs ?_ hfinite hdensity
  intro x hx
  exact ⟨⟨x, subset_closure (Submodule.subset_span hx)⟩, rfl⟩

/-- The one-dimensional rectifiability threshold of every real Hilbert space is at most
`6934 / 10000`, including nonseparable Hilbert spaces. -/
theorem sigmaOne_le_6934_div_10000 : sigmaOne E ≤ 6934 / 10000 := by
  exact sigmaOne_le_of_forall_gt E (by norm_num)
    fun _ hβ ↦ forcesOneRectifiability_of_gt E hβ

end InnerProductSpace

/-- Every threshold above `barS` forces one-rectifiability in the plane. -/
theorem forcesOneRectifiability_plane_of_barS_lt {β : ℝ} (hβ : barS < β) :
    ForcesOneRectifiability (EuclideanSpace ℝ (Fin 2)) (ENNReal.ofReal β) :=
  forcesOneRectifiability_of_gt _ (by rwa [← barS_eq])

/-- The planar one-dimensional rectifiability threshold is at most `6934/10000`. -/
theorem sigmaOne_plane_le_barS :
    sigmaOne (EuclideanSpace ℝ (Fin 2)) ≤ 6934 / 10000 :=
  sigmaOne_le_6934_div_10000 _

end Besicovitch
