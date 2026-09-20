/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Besicovitch.Rectifiability.Basic

/-!
# Isometric transport of density and rectifiability

Finite-length sets contained in an isometrically embedded subspace can be studied
in that subspace without changing their density or the resulting rectifiability.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal MeasureTheory

namespace Besicovitch

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Lower one-density is invariant under an isometry onto its image. -/
theorem lowerOneDensity_isometry_image {f : X → Y} (hf : Isometry f) (s : Set X) (x : X) :
    lowerOneDensity (f '' s) (f x) = lowerOneDensity s x := by
  unfold lowerOneDensity
  congr 1
  funext r
  congr 1
  rw [← hf.hausdorffMeasure_image (Or.inl (by norm_num)) (s ∩ Metric.ball x r)]
  rw [← hf.preimage_ball x r, image_inter_preimage]

/-- Isometric images of countably one-rectifiable sets are countably one-rectifiable. -/
theorem IsCountablyOneRectifiable.isometry_image {s : Set X}
    (hs : IsCountablyOneRectifiable s) {f : X → Y} (hf : Isometry f) :
    IsCountablyOneRectifiable (f '' s) := by
  obtain ⟨g, hg, hnull⟩ := hs
  refine ⟨fun n ↦ f ∘ g n, ?_, ?_⟩
  · intro n
    obtain ⟨K, hK⟩ := hg n
    exact ⟨K, by simpa using hf.lipschitz.comp hK⟩
  · apply measure_mono_null ?_ ((hf.hausdorffMeasure_image
      (Or.inl (by norm_num)) (s \ ⋃ n, range (g n))).trans hnull)
    rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro hxg
    obtain ⟨n, t, ht⟩ := mem_iUnion.mp hxg
    exact hy (mem_iUnion.mpr ⟨n, t, congrArg f ht⟩)

/-- A forcing theorem in an isometric subspace applies to measurable sets contained in its image. -/
theorem rectifiable_of_forcesOneRectifiability_of_isometry {f : X → Y}
    (hf : Isometry f) {beta : ℝ≥0∞} (hforce : ForcesOneRectifiability X beta)
    {s : Set Y} (hs : MeasurableSet s) (hsrange : s ⊆ range f)
    (hfinite : μH[1] s < ∞)
    (hdensity : ∀ᵐ x ∂μH[1].restrict s, beta ≤ lowerOneDensity s x) :
    IsCountablyOneRectifiable s := by
  have himage : f '' (f ⁻¹' s) = s := image_preimage_eq_of_subset hsrange
  have hmeasure : μH[1] (f ⁻¹' s) = μH[1] s := by
    rw [hf.hausdorffMeasure_preimage (Or.inl (by norm_num)), inter_eq_left.mpr hsrange]
  have hmap : Measure.map f (μH[1].restrict (f ⁻¹' s)) = μH[1].restrict s := by
    rw [← Measure.restrict_map hf.continuous.measurable hs,
      hf.map_hausdorffMeasure (Or.inl (by norm_num)), Measure.restrict_restrict hs,
      inter_eq_left.mpr hsrange]
  have hpre : ∀ᵐ x ∂μH[1].restrict (f ⁻¹' s),
      beta ≤ lowerOneDensity (f ⁻¹' s) x := by
    have h := ae_of_ae_map hf.continuous.measurable.aemeasurable (hmap.symm ▸ hdensity)
    filter_upwards [h] with x hx
    rwa [← himage, lowerOneDensity_isometry_image hf] at hx
  have hrect := hforce (f ⁻¹' s) (hs.preimage hf.continuous.measurable)
    (hmeasure ▸ hfinite) hpre
  simpa only [himage] using hrect.isometry_image hf

end Besicovitch
