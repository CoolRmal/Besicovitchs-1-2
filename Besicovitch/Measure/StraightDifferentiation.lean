/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Besicovitch.BPC.Defs
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Small-ball estimates for measures singular to a straight measure

The metric five-ball covering lemma replaces finite-dimensional differentiation.
A measure singular to a straight measure has ball mass `o(r)` almost everywhere
for the straight measure. No ambient Besicovitch covering theorem is needed.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory Topology

namespace Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- A straight measure assigns at most `2r` mass to a closed ball of radius `r`. -/
theorem IsStraightMeasure.measure_closedBall_le {mu : Measure X}
    (hmu : IsStraightMeasure mu) (z : X) (r : ℝ) :
    mu (Metric.closedBall z r) ≤ ENNReal.ofReal (2 * r) := by
  apply (hmu _ measurableSet_closedBall).trans
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  have hxz : dist x z ≤ r := Metric.mem_closedBall.mp hx
  have hzy : dist z y ≤ r := by simpa [dist_comm] using Metric.mem_closedBall.mp hy
  exact (dist_triangle x z y).trans (by linarith)

variable [SecondCountableTopology X]

/-- Fivefold enlargement turns a lower ball estimate for `nu` into an upper estimate
for a straight measure of the set of centers. -/
theorem IsStraightMeasure.measure_le_of_ball_cover {mu nu : Measure X}
    (hmu : IsStraightMeasure mu) {s U : Set X} {k : ℝ} (hk : 0 < k)
    (hballs : ∀ x ∈ s, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      Metric.closedBall x r ⊆ U ∧ ENNReal.ofReal (k * r) ≤ nu (Metric.closedBall x r)) :
    mu s ≤ ENNReal.ofReal (10 / k) * nu U := by
  classical
  choose r hr hr1 hrU hrmass using fun x : s ↦ hballs x x.property
  obtain ⟨u, -, hdisjoint, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
      (univ : Set s) (fun x ↦ (x : X)) r 1 (fun x _ ↦ hr1 x) 5 (by norm_num)
  have hcountable : u.Countable :=
    hdisjoint.countable_of_nonempty_interior fun x _ ↦
      (Metric.nonempty_ball.mpr (hr x)).mono Metric.ball_subset_interior_closedBall
  letI : Countable u := hcountable.to_subtype
  have hscover : s ⊆ ⋃ x : u, Metric.closedBall (x : X) (5 * r x) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover ⟨x, hx⟩ (mem_univ _)
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy (Metric.mem_closedBall_self (hr ⟨x, hx⟩).le)⟩
  have hmass (x : u) : mu (Metric.closedBall (x : X) (5 * r x)) ≤
      ENNReal.ofReal (10 / k) * nu (Metric.closedBall (x : X) (r x)) := by
    calc
      mu (Metric.closedBall (x : X) (5 * r x)) ≤
          ENNReal.ofReal (2 * (5 * r x)) := hmu.measure_closedBall_le _ _
      _ = ENNReal.ofReal (10 / k) * ENNReal.ofReal (k * r x) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 10 / k)]
        congr 1
        field_simp
        ring
      _ ≤ ENNReal.ofReal (10 / k) * nu (Metric.closedBall (x : X) (r x)) := by
        gcongr
        exact hrmass x
  have hdisjoint' : Pairwise fun x y : u ↦
      Disjoint (Metric.closedBall (x : X) (r x)) (Metric.closedBall (y : X) (r y)) :=
    hdisjoint.subtype
  calc
    mu s ≤ mu (⋃ x : u, Metric.closedBall (x : X) (5 * r x)) := measure_mono hscover
    _ ≤ ∑' x : u, mu (Metric.closedBall (x : X) (5 * r x)) := measure_iUnion_le _
    _ ≤ ∑' x : u, ENNReal.ofReal (10 / k) *
        nu (Metric.closedBall (x : X) (r x)) := ENNReal.tsum_le_tsum hmass
    _ = ENNReal.ofReal (10 / k) *
        nu (⋃ x : u, Metric.closedBall (x : X) (r x)) := by
      rw [ENNReal.tsum_mul_left, measure_iUnion hdisjoint' (fun _ ↦ measurableSet_closedBall)]
    _ ≤ ENNReal.ofReal (10 / k) * nu U := by
      gcongr
      exact iUnion_subset fun x ↦ hrU x

variable [BorelSpace X]

/-- A measure singular to a straight measure has arbitrarily small linear ball bounds
at almost every point for the straight measure. -/
theorem IsStraightMeasure.ae_exists_scale_measure_closedBall_lt
    {mu nu : Measure X} [IsFiniteMeasure nu]
    (hmu : IsStraightMeasure mu) (hsingular : nu ⟂ₘ mu) {k : ℝ} (hk : 0 < k) :
    ∀ᵐ x ∂mu, ∃ scale : ℝ, 0 < scale ∧ ∀ r : ℝ, 0 < r → r < scale →
      nu (Metric.closedBall x r) < ENNReal.ofReal (k * r) := by
  obtain ⟨A, hA, hnuA, hmuAc⟩ := hsingular
  let bad : Set X := {x | x ∈ A ∧ ∀ scale : ℝ, 0 < scale →
    ∃ r : ℝ, 0 < r ∧ r < scale ∧ ENNReal.ofReal (k * r) ≤ nu (Metric.closedBall x r)}
  have hbad : mu bad = 0 := by
    apply le_antisymm ?_ bot_le
    apply ENNReal.le_of_forall_pos_le_add
    intro epsilon hepsilon _
    let c := ENNReal.ofReal (10 / k)
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity : 0 < 10 / k)).ne'
    have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
    have htol : 0 < (epsilon : ℝ≥0∞) / c :=
      ENNReal.div_pos (by exact_mod_cast hepsilon.ne') hctop
    obtain ⟨U, hAU, hU, hnuU⟩ := A.exists_isOpen_lt_of_lt (μ := nu) _ (hnuA ▸ htol)
    have hcover : ∀ x ∈ bad, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
        Metric.closedBall x r ⊆ U ∧
          ENNReal.ofReal (k * r) ≤ nu (Metric.closedBall x r) := by
      intro x hx
      obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hAU hx.1))
      obtain ⟨r, hr, hrsmall, hrmass⟩ := hx.2 (min 1 delta) (lt_min zero_lt_one hdelta)
      refine ⟨r, hr, (hrsmall.trans_le (min_le_left _ _)).le, ?_, hrmass⟩
      exact (Metric.closedBall_subset_ball (hrsmall.trans_le (min_le_right _ _))).trans hball
    have hbound := hmu.measure_le_of_ball_cover hk hcover
    calc
      mu bad ≤ c * nu U := hbound
      _ ≤ c * ((epsilon : ℝ≥0∞) / c) := by gcongr
      _ = 0 + (epsilon : ℝ≥0∞) := by
        rw [ENNReal.mul_div_cancel hc0 hctop, zero_add]
  have haebad : ∀ᵐ x ∂mu, x ∉ bad := by
    simpa only [ae_iff, not_not, setOf_mem_eq] using hbad
  have haeA : ∀ᵐ x ∂mu, x ∈ A := by
    rwa [ae_iff]
  filter_upwards [haebad, haeA] with x hx hxA
  by_contra hnot
  push Not at hnot
  exact hx ⟨hxA, hnot⟩

end Besicovitch
