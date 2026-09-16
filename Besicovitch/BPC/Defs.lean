/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Besicovitch.Statement

/-!
# The Besicovitch pair condition

This file defines straight measures and the pair condition in a metric measurable space.  The
rectifiability consequences are developed for finite-dimensional real normed spaces; the
six-point transfer instantiates the condition in the Euclidean plane.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Besicovitch

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

end Besicovitch
