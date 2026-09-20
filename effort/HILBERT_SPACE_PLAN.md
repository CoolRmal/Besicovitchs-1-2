# Infinite-dimensional Hilbert-space extension

The target is the existing definition of `sigmaOne`, with `CompleteSpace` replacing
`FiniteDimensional` in the two general challenge declarations. Definitions of density,
Hausdorff measure, and rectifiability are not to be changed.

## Why completeness cannot simply be omitted

This section is a mathematical argument, not a Lean-certified counterexample.
The distinction matters because `IsCountablyOneRectifiable` uses Lipschitz maps defined
on all of the real line. In an incomplete space this is stronger than using maps from
arbitrary subsets of the real line.

In real square-summable sequence space consider the smooth bi-Lipschitz arc

$$
v(t)=(2^{-k}t^k)_{k\geq0},\qquad 0\leq t\leq1.
$$

The derivative never vanishes (its coordinate with index 1 is 1/2). Any finite
collection of distinct points on the arc is linearly independent, by the Vandermonde
determinant applied to its first finitely many coordinates.

Let A be a Bernstein subset of the open unit interval: both A and its complement
meet every nonempty perfect subset of that interval. Such sets exist using choice.
Neither A nor its complement contains an uncountable compact set. In particular,
each has inner Lebesgue measure zero, and A has full outer measure locally.
Put

$$
V=\operatorname{span}_{\mathbb R}\{v(t):t\in A\},\qquad S=v(A).
$$

Give V the inherited real inner product. Finite linear independence implies

$$
V\cap v([0,1])=S.
$$

Thus S is closed in V and is Borel there, even though it is not Borel in the
completion. Isometries preserve Hausdorff outer measure. For every Borel subset B
of the whole arc, the set S intersect B has the same outer length as B: any
positive-length measurable subset of B disjoint from S would contain a
positive-length compact subset, whose parameter set would contain a perfect set
disjoint from A. Consequently S has positive finite length and

$$
\lim_{r\downarrow0}\frac{\mathcal H^1(S\cap B_V(v(t),r))}{2r}=1
\quad(t\in A).
$$

On the other hand, for a Lipschitz map f from the real line to V, each
f([-m,m]) intersect S is compact: S is relatively closed and f([-m,m]) is compact.
Every compact subset of S is countable, by the Bernstein property and the
homeomorphism v. Therefore S meets the range of each such f in a null set.
No countable family of global Lipschitz curves covers S up to a null set.

In particular, `ForcesOneRectifiability V beta` fails for every real threshold
between 0 and 1. The admissible-threshold set is nonempty: the usual 5r covering
estimate gives a universal finite upper bound on lower Hausdorff density in
separable metric spaces. To see nonemptiness without a sharp density theorem,
a positive finite-measure set with lower density greater than 5 would admit,
inside arbitrarily small open neighborhoods of the set, a disjoint family of
small balls whose fivefold enlargements cover it. Summing their diameters gives
H1(S) at most 5/beta times H1(S), a contradiction when beta > 5. Finite-length
sets are separable, so the same argument applies setwise in any metric space.
Hence sigmaOne(V) is at least 1, ruling out the proposed 0.6934 bound without
completeness under the repository's definitions.

Passing to the completion does not fix this example: S is not Borel in the
completion, and curves in the completion need not take values in V.

## Formalized proof

The six-point estimate and its transfer to the Besicovitch pair condition already
work in arbitrary real inner-product spaces, without completeness or separability.
The extension is in the measure-to-rectifiability argument:

- `Geometry/CompactConvexHull.lean` proves compactness of closed convex hulls of compact
  sets in complete normed spaces. Attachments, finite-length continuum parametrization,
  and countable surgery now use completeness instead of finite dimensionality.
- `Measure/StraightDifferentiation.lean` proves the required small-ball estimate by
  the metric five-ball covering theorem. This replaces finite-dimensional measure
  differentiation in density localization and the choice of a density point.
- `Measure/HausdorffSeparable.lean` proves separability of finite-length sets directly
  from countable Hausdorff covers. `Rectifiability/Isometry.lean` transports density
  and rectifiability isometrically.
- `Main/RationalBound.lean` applies the separable Banach-space bridge to the closed
  linear span of each finite-length set, then transports the curves back.
- `Challenge.lean` and `Solution.lean` now use `CompleteSpace` rather than
  `FiniteDimensional` in both general declarations. The definitions and comparator
  configuration are unchanged.

All three local targets (`Besicovitch`, `Challenge`, and `Solution`) build. The five
compared solution declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
The Linux GitHub Actions comparator job independently checks the submitted declarations.
