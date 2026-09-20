/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Separability of finite-length sets

Countable Hausdorff covers at arbitrarily small scales give a countable dense set.
This lets us work in a separable closed linear subspace without assuming that the
ambient Hilbert space is separable.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal MeasureTheory

namespace Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A set of finite Hausdorff one-measure has countable covers of arbitrarily small diameter. -/
theorem exists_small_diameter_cover_of_hausdorffMeasure_lt_top {s : Set X}
    (hs : μH[1] s < ∞) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ t : ℕ → Set X,
      s ⊆ ⋃ n, t n ∧ ∀ n, Metric.ediam (t n) ≤ ENNReal.ofReal epsilon := by
  rw [Measure.hausdorffMeasure_apply] at hs
  have h := lt_of_le_of_lt
    (le_iSup_of_le (ENNReal.ofReal epsilon)
      (le_iSup_of_le (ENNReal.ofReal_pos.mpr hepsilon) le_rfl)) hs
  simp only [iInf_lt_iff] at h
  obtain ⟨t, ht, hdiam, -⟩ := h
  exact ⟨t, ht, hdiam⟩

/-- Finite Hausdorff one-measure implies separability, without completeness. -/
theorem isSeparable_of_hausdorffMeasure_lt_top {s : Set X} (hs : μH[1] s < ∞) :
    IsSeparable s := by
  classical
  by_cases hsne : s.Nonempty
  · letI : Nonempty X := hsne.to_subtype.map Subtype.val
    have hc (n : ℕ) := exists_small_diameter_cover_of_hausdorffMeasure_lt_top
      hs (by positivity : 0 < 1 / (n + 1 : ℝ))
    choose t ht hdiam using hc
    let p (n m : ℕ) : X :=
      if h : (t n m).Nonempty then h.some else Classical.choice ‹Nonempty X›
    refine ⟨range (Function.uncurry p), countable_range _, ?_⟩
    intro x hx
    apply Metric.mem_closure_iff.mpr
    intro epsilon hepsilon
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hepsilon
    obtain ⟨m, hm⟩ := mem_iUnion.mp (ht n hx)
    have hnonempty : (t n m).Nonempty := ⟨x, hm⟩
    have hp : p n m ∈ t n m := by
      simpa only [p, dif_pos hnonempty] using hnonempty.some_mem
    refine ⟨p n m, ⟨(n, m), rfl⟩, ?_⟩
    have hed := (Metric.edist_le_ediam_of_mem hm hp).trans (hdiam n m)
    have hd : dist x (p n m) ≤ 1 / (n + 1 : ℝ) := by
      simpa only [edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity :
        0 ≤ 1 / (n + 1 : ℝ))] using hed
    exact hd.trans_lt hn
  · rw [not_nonempty_iff_eq_empty.mp hsne]
    exact countable_empty.isSeparable

end Besicovitch
