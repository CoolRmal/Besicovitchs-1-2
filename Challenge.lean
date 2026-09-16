/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Challenge: the planar Besicovitch threshold

Every transparent definition occurring in the theorem statements, and the statements.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory NNReal Topology

namespace Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The lower one-density of `s` at `x`, normalized by the diameter `2 * r` of a ball. -/
def lowerOneDensity (s : Set X) (x : X) : ℝ≥0∞ :=
  liminf (fun r : ℝ ↦ μH[1] (s ∩ Metric.ball x r) / ENNReal.ofReal (2 * r))
    (nhdsWithin 0 (Ioi 0))

/-- A set is countably one-rectifiable if Lipschitz curves cover it up to Hausdorff null measure. -/
def IsCountablyOneRectifiable (s : Set X) : Prop :=
  ∃ f : ℕ → ℝ → X,
    (∀ i, ∃ K : ℝ≥0, LipschitzWith K (f i)) ∧ μH[1] (s \ ⋃ i, range (f i)) = 0

/-- Every finite-measure set with lower density at least `β` is one-rectifiable. -/
def ForcesOneRectifiability (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (β : ℝ≥0∞) : Prop :=
  ∀ s : Set X, MeasurableSet s → μH[1] s < ∞ →
    (∀ᵐ x ∂μH[1].restrict s, β ≤ lowerOneDensity s x) →
      IsCountablyOneRectifiable s

/-- The infimum of the nonnegative thresholds forcing one-rectifiability in `X`. -/
def sigmaOne (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] : ℝ :=
  sInf {β : ℝ | 0 ≤ β ∧ ForcesOneRectifiability X (ENNReal.ofReal β)}

/-- The extended distance between two sets; it is infinite when either set is empty. -/
def setEDist {X : Type*} [PseudoEMetricSpace X] (s t : Set X) : ℝ≥0∞ :=
  ⨅ x ∈ s, ⨅ y ∈ t, edist x y

/-- A measure is straight if every measurable set has mass at most its extended diameter. -/
def IsStraightMeasure {E : Type*} [MetricSpace E] [MeasurableSpace E] (μ : Measure E) : Prop :=
  ∀ s, MeasurableSet s → μ s ≤ Metric.ediam s

/-- The Besicovitch pair condition at density parameter `β`. -/
def BesicovitchPairCondition (E : Type*) [MetricSpace E] [MeasurableSpace E] (β : ℝ) : Prop :=
  ∀ μ : Measure E, IsStraightMeasure μ →
    ∃ τ : ℝ, 0 < τ ∧ ∀ scale : ℝ, 0 < scale →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ e₁ e₂ : Set E,
          MeasurableSet e₁ → MeasurableSet e₂ →
          e₁.Nonempty → e₂.Nonempty → 0 < setEDist e₁ e₂ →
          setEDist e₁ e₂ < ENNReal.ofReal δ →
          (∀ x ∈ e₁ ∪ e₂, ∀ r : ℝ, 0 < r → r < scale →
            ENNReal.ofReal (2 * β * r) < μ (Metric.ball x r)) →
          ∃ v : Set E,
            IsOpen v ∧ (v ∩ e₁).Nonempty ∧ (v ∩ e₂).Nonempty ∧
            ENNReal.ofReal τ * Metric.ediam v < μ (v \ (e₁ ∪ e₂))

/-- Every threshold strictly above `6934 / 10000` forces one-rectifiability in the plane. -/
theorem forcesOneRectifiability_plane_of_gt (β : ℝ) (hβ : 6934 / 10000 < β) :
    ForcesOneRectifiability (EuclideanSpace ℝ (Fin 2)) (ENNReal.ofReal β) := by
  sorry

/-- The planar threshold is at least `1 / 2`: Besicovitch's purely unrectifiable graph has lower
density `1 / 2`. -/
theorem one_half_le_sigma_one_plane :
    (1 / 2 : ℝ) ≤ sigmaOne (EuclideanSpace ℝ (Fin 2)) := by
  sorry

/-- The planar threshold is at most `6934 / 10000`, below the published record `7 / 10`. -/
theorem sigma_one_plane_le_6934_div_10000 :
    sigmaOne (EuclideanSpace ℝ (Fin 2)) ≤ 6934 / 10000 := by
  sorry

end Besicovitch

namespace Besicovitch

/-- In every real inner product space, every density parameter above `6934 / 10000` satisfies the
Besicovitch pair condition. -/
theorem besicovitchPairCondition_of_gt_6934_div_10000 (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (β : ℝ)
    (hβ : 6934 / 10000 < β) : BesicovitchPairCondition E β := by
  sorry

/-- In every finite-dimensional real inner product space, in particular in every `ℝⁿ`, each
threshold above `6934 / 10000` forces one-rectifiability. -/
theorem forcesOneRectifiability_of_gt_6934_div_10000 (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (β : ℝ) (hβ : 6934 / 10000 < β) : ForcesOneRectifiability E (ENNReal.ofReal β) := by
  sorry

/-- The threshold of every finite-dimensional real inner product space, in particular
of every `ℝⁿ`, is at most `6934 / 10000`. -/
theorem sigma_one_le_6934_div_10000 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    sigmaOne E ≤ 6934 / 10000 := by
  sorry

end Besicovitch
