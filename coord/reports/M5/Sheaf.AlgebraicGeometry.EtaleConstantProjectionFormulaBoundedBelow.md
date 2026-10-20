## What changed

Change record: `coord/changes/M5-constant-projection-transformation.md`.

The bounded-below theorem is reduced by naturality, degree by degree, to bounded flat
coefficients. The reduction uses the original canonical counit-mate transformation.
Its two functors are named in `EtaleConstantProjectionMap`, with proved comparison,
shift and exactness APIs. Existing public imports, declaration signatures and the
body defining the canonical map are retained verbatim.

The new flat-approximation module constructs the bounded flat quotient and proves
that it computes either functor in the chosen cohomological degree. It uses flat
integer representatives, flat kernels over a PID, the existing generic K-flat API,
and the long exact sequence of the high stupid-tail triangle. The remaining bounded
flat comparison is a separate source result from Stacks Tag 0F0E.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.isIso_constantDerivedProjectionMap_of_boundedBelow`.

The new theorem
`AlgebraicGeometry.Etale.exists_constantProjection_boundedFlat_approximation`
is proved, including its private flat-model, lower-bound and truncation helpers.
The final map, bounded-flat statement, approximation and main theorem compiled in
7.2, 2.7, 9.7 and 3.8 seconds. The current unchanged J5 consumer compiled in 26.2 seconds.
`#print axioms` for this new approximation and the target-functor exactness API shows
only `propext`, `Classical.choice`, and `Quot.sound`. The original bounded-below theorem
still depends on `sorryAx` through the separate bounded-flat source case.

Added one hole, remaining in the public theorem
`AlgebraicGeometry.Etale.isIso_constantDerivedProjectionMap_of_bounded_flat`.
Its conclusion concerns a bounded flat complex only; its docstring gives the
finite-free, Lazard, Postnikov and finite stupid-truncation argument. No definition
contains a hole. This is a decomposition: one upper hole closed and one strictly
smaller hole added, no net reduction among the holes edited or introduced here. Import-closure pruning
is counted separately by the ledger. It is not an axiom-free proof of the original theorem.

## No longer needed

The original parent proof dependencies below are not used by the replacement route:
`def-pc-kflat-complex`, `lem-pc-bounded-above-flat-kflat-site`,
`lem-pc-filtered-colimit-derived-tensor`,
`lem-pc-module-filtered-colimits-tensor`,
`lem-weil-pbc-abelian-etale-sheaves-grothendieck`, and
`lem-weil-pbc-ringed-projection-mate-exact`.

The generic `ObjectProperty.kFlat` API supplies the actual tensor category used
here. The bounded-flat comparison needs ordinary tensor and filtered cohomology,
not a general filtered-colimit theorem for derived tensor. Mathlib supplies the
Grothendieck sheaf instance. The ringed-site projection lemma has a different
coefficient category. No source-library declaration is removed or re-holed.

Direct proof imports removed from the parent:
`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`,
`Sheaf.Algebra.Homology.KFlat`,
`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`,
`Sheaf.Algebra.Homology.FilteredColimitDerivedTensor`,
`WeilConjectures.Algebra.Homology.FilteredColimitsTensor`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`,
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact`,
`WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`,
`WeilConjectures.CategoryTheory.RightDerivedFunctorTruncationIso`,
`Mathlib.RingTheory.Flat.TorsionFree`,
`Mathlib.AlgebraicGeometry.Sites.AffineEtale`,
`Mathlib.CategoryTheory.Sites.GlobalSections`,
`Sheaf.Paper.ProjectionMateExact`,
`WeilConjectures.CategoryTheory.TruncationTriangle`,
`Mathlib.Algebra.Homology.Embedding.CochainComplex`,
`Mathlib.Algebra.Homology.Single`,
`Mathlib.CategoryTheory.Triangulated.Triangulated`,
`Sheaf.Algebra.Homology.IntegerFlatRepresentative`,
`Sheaf.RingTheory.Flat.LazardPresentation`, and
`Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.
Some of these remain dependencies of the smaller replacement results; removal
from this direct import list does not claim their whole-library withdrawal.

## Where the brief, the DAG or earlier work was wrong

The ringed-site K-flat and projection APIs in the earlier plan do not directly
apply to the actual category of sheaves of integer modules. The generic complex
K-flat API does apply. The upper cutoff must kill both tail degrees n and n+1;
we choose N at least max(b,n-a+1).

The canonical derived comparison has expensive transparent instance conversions.
The interface extension names its natural transformation, functors, and shift
structures and provides proved formulas, keeping the existing map body verbatim.
Keep the lower-bound and cutoff proof generic until the final integer-module
specialization; this avoids repeatedly checking concrete sheaf-derived instance data.
The approximation helpers use the actual object and hom universe sizes of the
integer-module and sheaf categories, avoiding enlargement of their derived instances.
The accompanying change record lists its consumers and the implementation changes.
A concurrent J5 update added a cached-comparison API to the map module; that API and
its equation are preserved verbatim. FiniteMappingAdjunction was quarantined during
the session; its archive is unchanged, and its temporary validation copy is excluded.

## New nodes

`lem-kun-constant-projection-bounded-flat` records the bounded-flat source case.
`lem-kun-constant-projection-flat-approximation` records the independent, proved
bounded-quotient construction. Both nodes are in `sec-smooth-purity`.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
