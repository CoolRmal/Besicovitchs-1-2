/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Besicovitch.Main.Bound
public import Besicovitch.SixPoint.GramWeightedBound

/-!
# The rational bound in every real inner product space

The Gram certificates give the weighted geometric bound at the small rational weights, the finite
failure tree turns that into the six-point finite property at `barS = 6934/10000`, and the
six-point transfer turns that into the Besicovitch pair condition and the rectifiability bound.
None of these steps uses the dimension: the pair condition holds in every real inner product
space, and the bound on `sigmaOne` in every finite-dimensional one.  The planar statements are
the instances at `EuclideanSpace ℝ (Fin 2)`.
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

variable [FiniteDimensional ℝ E]

/-- Every threshold above `6934 / 10000` forces one-rectifiability in a finite-dimensional real
inner product space. -/
theorem forcesOneRectifiability_of_gt {β : ℝ} (hβ : 6934 / 10000 < β) :
    ForcesOneRectifiability E (ENNReal.ofReal β) :=
  (sixPointFiniteProperty_barS E).forcesOneRectifiability_of_gt barS_pos barS_lt_one
    (by rwa [barS_eq])

/-- The one-dimensional rectifiability threshold of a finite-dimensional real inner product space
is at most `6934 / 10000`. -/
theorem sigmaOne_le_6934_div_10000 : sigmaOne E ≤ 6934 / 10000 := by
  simpa only [barS_eq] using sigmaOne_le_barS_of_sixPointFiniteProperty
    (sixPointFiniteProperty_barS E)

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
