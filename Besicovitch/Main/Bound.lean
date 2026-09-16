/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Besicovitch.SixPoint.RationalChord
public import Besicovitch.BPC.Rectifiability
public import Besicovitch.BPC.SixPointTransfer
public import Besicovitch.Certificates.EndpointBridge

/-!
# The six-point bound for the density threshold

This file contains the analytic bridge from the finite six-point property to the upper bound on
the rectifiability threshold of a finite-dimensional real normed space.  The finite property
itself remains the sole geometric input.
-/

@[expose] public section

noncomputable section

namespace Besicovitch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A positive subunit parameter satisfying the Besicovitch pair condition bounds the
rectifiability threshold of a finite-dimensional real normed space. -/
theorem BesicovitchPairCondition.sigmaOne_le {s : ℝ} (hpair : BesicovitchPairCondition E s)
    (hs : 0 < s) (hs_one : s < 1) : sigmaOne E ≤ s := by
  apply sigmaOne_le_of_forall_gt E hs.le
  intro gamma hs_gamma
  exact hpair.forcesOneRectifiability hs hs_one hs_gamma

/-- The finite six-point property at a positive subunit parameter forces one-rectifiability
at every larger threshold. -/
theorem SixPointFiniteProperty.forcesOneRectifiability_of_gt {s : ℝ}
    (hfinite : SixPointFiniteProperty E s) (hs : 0 < s) (hs_one : s < 1) {gamma : ℝ}
    (hs_gamma : s < gamma) :
    ForcesOneRectifiability E (ENNReal.ofReal gamma) := by
  let beta := (s + min gamma 1) / 2
  have hs_min : s < min gamma 1 := lt_min_iff.mpr ⟨hs_gamma, hs_one⟩
  have hs_beta : s < beta := by
    dsimp only [beta]
    linarith
  have hbeta_min : beta < min gamma 1 := by
    dsimp only [beta]
    linarith
  have hbeta_gamma : beta < gamma := hbeta_min.trans_le (min_le_left _ _)
  have hbeta_one : beta < 1 := hbeta_min.trans_le (min_le_right _ _)
  have hpair : BesicovitchPairCondition E beta :=
    hfinite.besicovitchPairCondition hs hs_beta
  exact hpair.forcesOneRectifiability (hs.trans hs_beta) hbeta_one hbeta_gamma

/-- The finite six-point property at a positive subunit parameter bounds the rectifiability
threshold by that parameter. -/
theorem SixPointFiniteProperty.sigmaOne_le {s : ℝ}
    (hfinite : SixPointFiniteProperty E s) (hs : 0 < s) (hs_one : s < 1) :
    sigmaOne E ≤ s :=
  sigmaOne_le_of_forall_gt E hs.le
    fun _ hs_gamma ↦ hfinite.forcesOneRectifiability_of_gt hs hs_one hs_gamma

/-- The desired bound follows from the finite six-point property at the certified endpoint. -/
theorem sigmaOne_le_barS_of_sixPointFiniteProperty
    (hfinite : SixPointFiniteProperty E barS) :
    sigmaOne E ≤ barS :=
  hfinite.sigmaOne_le barS_pos barS_lt_one

end Besicovitch
