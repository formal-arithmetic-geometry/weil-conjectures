## What changed

Replaced the proof hole in `AlgebraicGeometry.Etale.etaleGenericPerfectHom`, preserving its
mathematical statement, public imports, and evaluation-induced comparison. The proof uses the existing
source-library site-perfect/dualizable interface, flat-model Tor-amplitude theorems, and
canonical internal-Hom pullback comparison. Only the item's Lean module is adapted.
The new transparent definition `derivedHomRightEvaluation` is exactly the canonical
symmetry followed by the tensor–Hom counit. The two evaluation lets name this composite
to avoid expensive kernel comparisons at module coefficients. A theorem with the complete
old signature, including its original evaluation terms, compiles by applying the new theorem.
See `coord/changes/etale-generic-perfect-hom-evaluation.md`; its sole downstream importer,
`Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed` (B8), needs no edit.

The finite-projective local models give site-perfectness and local Tor amplitude `[a,b]`.
Exact pullback and conservativity of an étale cover descend that Tor interval to `P`.
Duality gives the interval `[-b,-a]` for its dual, so tensoring with `N` gives the required
`[c-b,d-a]` bound for internal Hom. The canonical comparison is invertible because `P` is
dualizable; its evaluation identity and braidedness of derived pullback give the precise
formula in the statement. Exact inverse image transports the bound to the target.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Etale.etaleGenericPerfectHom`
(`lem-sf-etale-generic-perfect-hom`). Holes added: 0. Holes remaining: 0. Split off: 0.
All private helper lemmas are proved. The new definition
`AlgebraicGeometry.Etale.derivedHomRightEvaluation` is an explicit canonical composite,
with no postponed data. Four DAG attachments point to existing proved source declarations;
no new source obligation is introduced.

The full proof has compiled without errors or warnings. An independent scratch theorem
with the original signature compiled in 47.0 seconds using the completed theorem directly.
The final delivery preflight performs the axiom and consumer checks.

## No longer needed

The proof replaces the chartwise Hom-complex construction with the existing duality API.
Removed proof imports:

- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel`
- `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose`
- `Sheaf.AlgebraicGeometry.EtaleLocalDualInterval`
- `Sheaf.CategoryTheory.RingedSitePerfectDuality`
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
- `Sheaf.Paper.CoefficientRingedTensorHomModel`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.SixFunctors.EtaleFiniteProjectivePullbackHom`
- `Sheaf.SixFunctors.EtaleHomComplexPullback`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Etale.Derived.Triangulated`

These are unnecessary direct proof dependencies of this item; this does not assert that
other targets cease to reach them. The exact inverse-image and cover-local conservativity
facts are used through the source library. Perfect duality, tensor amplitude, and canonical
comparison coherence are likewise used through already proved source declarations.


The original proof dependencies now unused directly are
`def-coef-hom-representative-evaluation`, `def-coef-ringed-tensor-hom-model`,
`def-kun-truncations`, `lem-kun-derived-tensor-triangulated`,
`lem-sf-derived-homology-long-exact`, `lem-sf-etale-finite-projective-pullback-hom`,
`lem-sf-etale-hom-complex-pullback`, `lem-sf-etale-local-dual-interval`,
`lem-sf-ringed-derived-closed-symmetric-monoidal`,
`lem-sfb-ringed-derived-monoidal-comparisons`, `lem-sfb-ringed-site-perfect-duality`,
`lem-weil-pbc-ringed-internal-hom-exact-restriction`,
`lem-weil-pbc-ringed-site-bounded-free-rhom-model`, and
`lem-weil-pbc-ringed-slice-evaluation-transpose`. The tensor-triangulated and derived-monoidal
comparison entries of the old top-level `tool_uses` list are removed: the source flat-model
and internal-Hom APIs contain the needed generic arguments. No unit statement or step is
withdrawn.


## Where the brief, the DAG or earlier work was wrong

The planned chartwise model and gluing argument is much longer than the source library's
existing dualizability argument. No mathematical statement or unit-level route is changed.
The unit `sk-prop-sf-biduality-general` has no separately realized step that this replacement
bypasses. The source module's Q79/deferred-proof documentation predates this H8 delivery.

## New nodes

`lem-sf-source-etale-site-perfect-dualizable` attaches
`AlgebraicGeometry.Etale.DerivedCategory.IsSitePerfect.isDualizable` in
`WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect`.
It is the site-perfect-to-dualizable implication for any commutative coefficient ring.

`lem-sf-source-dual-tor-interval` attaches
`DerivedCategory.torAmplitudeIn_of_exactPairing` in
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`.
It reflects a specified Tor interval under a two-sided duality.

`lem-sf-source-tensor-cohomology-interval` attaches
`DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_left` in the same module.
It adds a Tor interval and a cohomology interval.

`lem-sf-source-etale-dualizable-hom-comparison` attaches the canonical comparison-isomorphism
and dual-tensor-identification declarations in
`WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom`.
Its scope allows arbitrary target complexes and arbitrary scheme morphisms.

All four source declarations were read with their surrounding hypotheses. Each is already
proved; these attachments add no Lean files or obligations. The source comparisons retain
the actual evaluation transpose. Searches of the blueprint, Mathlib, and existing DAG found
no exact node for these generic statements: the existing perfect-duality nodes concern
different ringed-site or coefficient interfaces, and the existing finite-coefficient
internal-Hom pullback blueprint node has the specific coefficient-stage hypotheses.
Edge cases checked include zero objects, empty schemes, equal interval endpoints, identity
pullback, and a sheaf shifted to either interval endpoint; the signs give `[c-b,d-a]`.
The change record is `coord/changes/etale-generic-perfect-hom-evaluation.md`.
The original theorem type and its named-evaluation spelling are definitionally equal;
all binders and public imports are preserved. No forced adaptation is required.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
