## What changed

Replaced the body of
`AlgebraicGeometry.BrownTowerComparison.brownTowerFiniteSiteComparison`
with an explicit categorical construction of the transported counit and Hom equivalence.
The theorem's signature and public imports are unchanged.

The counit is the inverse compact-support comparison followed by inverse site image
of the Brown counit and the site counit. The Hom map is explicitly compact-support
image of a morphism followed by that counit. Its bijectivity is proved by composing
site-counit Hom congruence, bounded full faithfulness, the Brown adjunction, the
other site adjunction, and compact-support comparison. Naturality of the actual
comparison identifies this composite with the specified Hom map. The same computation
proves compatibility with the Brown Hom equivalence, naturality in both variables,
and scalar compatibility; exact-derived additivity proves the sum equation.

The finite-evaluation comparison is constructed as the displayed paste of inverse
site evaluation, finite Brown evaluation, and direct site evaluation. Bounded full
faithfulness is derived from the invertible site unit rather than assumed. Compact
support preserves lower bounds by exact open extension and the right adjoint of
exact proper pullback, using `exactDerivedAdjunction_isGE`.

The new module `Sheaf.Paper.BrownTowerGeometricTransport` states the genuine earlier
geometric construction, before any exceptional counit or Hom equivalence is adjoined.
It chooses finite and geometric comparisons simultaneously: an arbitrary finite
support realization would not enforce the normalization required by the compact
comparison equation. No definition chooses data from an unproved existence theorem;
all new definitions take the geometric data as an explicit parameter, and the
existential result is eliminated only inside the proof of the existing theorem.

## Proved and sorry left

Closed the original syntactic hole in
`AlgebraicGeometry.BrownTowerComparison.brownTowerFiniteSiteComparison`
(node `lem-pur-brown-tower-finite-site-comparison`). Its combining proof has no
`sorry`. The private categorical, bound, counit, evaluation, and transport helpers
have complete proof bodies. The Hom transport, bounded-full-faithfulness, exact-image bounds and additivity,
and evaluation paste have passed isolated categorical compiles. The geometric
interface and the consumer helpers have also compiled. The final structure proof
installs its recorded finiteness witness locally. The assembled item compiled
with no warnings or errors through lcompile.py (15.0 seconds); the geometric
module had separately compiled. Delivery preflight is the final check.

Added one remaining hole:
`AlgebraicGeometry.BrownTowerComparison.brownTowerGeometricTransport_exists`
(node `lem-pur-brown-tower-geometric-transport`). This is the finite and geometric
construction in original Steps 1--10, before the transported Hom chain. Its conclusion
contains neither the transported counit nor its Hom equivalence, their naturality,
additivity, linearity or Brown compatibility, nor the evaluation paste, bounded full
faithfulness or compact-support bound proved in the consumer. One hole closed and
one added is a decomposition, with net zero holes closed; this report does not count
it as an unconditional proof of the geometric construction.

## No longer needed

Removed these private imports from the item:
`Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`,
`Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`,
`Sheaf.Paper.SemilinearDerivedSections`,
`Sheaf.Paper.EtaleCompactScalarCoherence`,
`Sheaf.CategoryTheory.SystemDerivedEvaluation`,
`Sheaf.CategoryTheory.SystemDerivedTransitionCoherence`,
`Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`,
`Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`,
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`,
`Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`,
`Mathlib.CategoryTheory.Yoneda`, `Mathlib.CategoryTheory.Adjunction.Mates`,
and `Mathlib.AlgebraicGeometry.Noetherian`.
Their geometric assertions remain dependencies of the new geometric-construction
node; no associated module is claimed globally unnecessary. The item retains
`Sheaf.CategoryTheory.ExactDerivedAdjunctionBounds`, and uses the new geometric
module, `Mathlib.CategoryTheory.HomCongr`, and the exact-derived-functor API.
The original geometric tool approvals move out of the item's proof dependency list
into the subproblem's proof; the exact-derived-bounds approval remains. No source
library declarations or modules were deleted. No modules are globally pruned.

## Where the brief, the DAG or earlier work was wrong

Edge cases: the categorical construction uses no nonzero-object, nonempty-site,
finite-field, constructibility or boundedness hypotheses beyond those explicitly
required for the geometric comparison. Zero C and B cause no special choice of maps;
the construction is the same composite and the Hom bijection remains valid. The
retained source argument includes identity quotient maps, nonflat quotient changes,
and extension evaluations above the chosen coefficient level. No extra hypothesis
on the field is added.

No disputed statement or change to the unit route. The finite package and geometric
comparisons must be chosen together: `FiniteEvaluation.lower` is not separately
pinned to a chosen canonical compact-support realization. Consequently the geometric
existence theorem is existential in H, rather than incorrectly claiming extension
of every possible finite package. The retained theorem matches the original
simultaneous existential statement. The source is Zheng Construction 4.1 and Lemmas
4.10, 5.16 and 5.22, with the original geometric comparison dependencies.

## New nodes

`lem-pur-brown-tower-geometric-transport`, in
`dag/nodes/sec-smooth-purity/lem-pur-brown-tower-geometric-transport.json`, records the
geometric construction strictly before the final transported adjunction Hom chain.
Its module contains the data interface and one named theorem with a source and a
natural-language proof. The item node's proof and proof dependencies now describe
the actual combining proof. No existing statement or definition is changed, so
there is no change record or forced adaptation.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
