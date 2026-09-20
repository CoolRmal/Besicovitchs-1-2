/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Convex.TotallyBounded
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Compact closed convex hulls

In a complete real normed space, the closed convex hull of a compact set is compact.
Unlike compactness of bounded closed balls, this does not require finite dimension.
-/

@[expose] public section

open Set

namespace Besicovitch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The closed convex hull of a compact set is compact in a complete real normed space. -/
theorem isCompact_closure_convexHull {s : Set E} (hs : IsCompact s) :
    IsCompact (closure (convexHull ℝ s)) :=
  (totallyBounded_convexHull E hs.totallyBounded).closure.isCompact_of_isClosed isClosed_closure

end Besicovitch
