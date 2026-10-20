## What changed

Restored Sheaf.AlgebraicGeometry.BottomFreeChainDerivedSquare from the complete archive
named in coord/rework.tsv. Migrated the DerivedPullback, BoundedAboveFlatRingedSpaceKFlat
and PerfectHomTransport imports to their adopted WeilConjectures versions. The private
tensorCounit helper now uses IsKFlatTensor and returns only the counit properties used by
the proof. Its unused left-derived universal-property conjunct is omitted; the source
specification and its proof are untouched. The public bottomFreeChain_derived_square
statement remains byte-for-byte the archive's.

The full bounded-flat/counit/naturality proof remains complete. Replaced normalization in
invertibility checks with explicit isomorphism components. Cached the actual abelian
structures and exactness instances and retained constructed comparisons behind typed
interfaces. Existing source restriction instances take priority over generic composition
and additivity searches. The private chartEquivalence
constructs the actual Modules.overEquiv with a proved equality API and an irreducible
attribute; explicit equality transport preserves both functor uses. No existing definition,
functor, witness or mathematical assumption changes. The final complete item compiled and exported
cleanly through lcompile.py --all in 35.3 seconds.

Restored the unclaimed direct consumer
Sheaf.AlgebraicGeometry.BottomFreeChainPullbackComparison, redirecting its public
DerivedPullback import to the source and lowering generic local instance priorities.
The original archive failed with unknown Scheme and HasDerivedCategory, reported as
privately imported. The consumer's public theorem signature and complete proof body remain
verbatim. Its final version compiled and exported cleanly in 39.1 seconds, after the square,
through lcompile.py --all. Both files emitted no warnings.

Updated the item's proof record and retargeted lem-pc-bounded-above-flat-kflat's Lean
attachment to the existing source theorem whose predicate matches derivedPullback_spec.
Neither source theorem nor its Sheaf twin is modified or removed.
Change record: coord/changes/R4-bottom-free-chain-upstream-restoration.md.

LeanFinder found generic pullback/composition lemmas but no exact square. Loogle did not
recognize Functor.leftDerivedUnique; msearch grep returned no match. Direct source searches
located the adopted interfaces and their proved exact-restriction instances.

## Proved and sorry left

Assigned zero-hole quarantine/API repair: holes closed 0 of 0, holes added 0, holes left 0.
AlgebraicGeometry.Scheme.bottomFreeChain_derived_square and its private tensorCounit and
finiteFree_flat and chartEquivalence_eq helpers are completely proved. The new private
chartEquivalence is an actual data construction, with no proof dependency or choice. The restored consumer theorem
AlgebraicGeometry.Scheme.bottomFreeChain_pullback_comparison and its private additivity
helper are also completely proved. There is no decomposition, new axiom or new public statement.

## No longer needed

Removed the unused private import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived.
Replaced obsolete Sheaf.AlgebraicGeometry.DerivedPullback,
Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat and
Sheaf.AlgebraicGeometry.PerfectHomTransport imports with their adopted source versions.
The consumer also replaces its obsolete public Sheaf derived-pullback import.
The helper's unused universal-property result is unnecessary to the square calculation.

No mathematical dependency node is pruned and no module is withdrawn. All seven original
proof dependencies and the unit route are retained. The quarantined item and its direct
parent are restored with their original Lean attachments and public statements.

## Where the brief, the DAG or earlier work was wrong

The archived item already has zero holes and a complete proof: this is an upstream-sync
repair. Changing its derived-pullback import alone leaves an incompatible K-flat predicate.
The bounded-flat node still pointed at the old Sheaf twin, and the direct parent retained
its own retired public import. These interfaces are repaired without changing any public
theorem hypothesis, conclusion or universe. No source-library declaration, target statement
or definition is modified. No new nodes are introduced.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
