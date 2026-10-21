## What changed

Completed `AlgebraicGeometry.ProEtale.CondensedRing.existsUnique_supportDerivedTensorComparison`
in `Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison`, preserving all public
signatures. Refactored the two support predicates through generic categorical
definitions with the same family type and normalization equations. Added private proof imports of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal` and
`Sheaf.Paper.InverseImageModuleFlat`.

The comparison is the existing generic left-derived tensor comparison, transported
along the canonical isomorphism between total left derivation and the termwise
exact derived functor. Private lemmas prove its naturality and the required square
on arbitrary complexes. The ordinary total-complex map agrees with the generic
oplax comparison by its existing summand uniqueness theorem. Uniqueness of the
derived family follows by replacing the second input by a flat resolution whose
pullback is K-flat, cancelling the invertible normalization maps, and transporting
along representative isomorphisms by naturality. The generic categorical argument
is checked before specializing to the sheaf module categories, avoiding expansion
of their large instance terms.

Updated the existing node's proof, proof dependencies and proof origin to record
this route, and attached `ExactDerivedTensorComparisonFamily` and
`ExactDerivedTensorNormalization` to that existing definition node. No new modules,
nodes, theorem statements, or mathematical hypotheses.

Definition implementation change:
`coord/changes/P1-condensed-pullback-tensor-generic-predicates.md`.
The old concrete predicates cause kernel checking to unfold deeply nested sheaf
instance proofs when applying the generic comparison, exceeding the compile limit.
The generic predicates keep the same instance data behind a constant. The exact
old and new bodies and all downstream users are recorded in the change record.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.ProEtale.CondensedRing.existsUnique_supportDerivedTensorComparison`
(node `def-sfb-condensed-pullback-tensor-comparison`).

Holes closed: 1 of 1. Holes added: 0. Holes remaining in this module: 0.
All added private helpers are proved. This is a proof, with no split-off statements.
Existing dependency statements are used as provided by the library.


Validation: the complete item compiles without warnings (57.1 s; a profiled
single-file check also passed at 35.8 s). A separate importer test using the
compiled item verifies both the original derived-tensor family type and the exact
published naturality equation (19.3 s). Another importer copies the entire old
normalization body verbatim and proves its equivalence with the new predicate by
`rfl` (24.2 s). Thus the complete old specification is definitionally unchanged.

Three unchanged consumers were tested against the item artifact:
`CondensedOpenClosedInternalHomMaps` (held by F4),
`CondensedSupportProjectionFormula` (unclaimed), and
`SixFunctors.ClosedImmersionTensorProjection` (unclaimed).
They fail with the same error headers and counts against the unchanged published
item: respectively 13, 2, and 1. The first lacks
`PreservesFiniteColimits (lowerStar Λ i)`; the latter two report kernel/generalize
errors from the changed `closedSupport_lowerStarExact` interface in the existing
closed-support dependencies. These are baseline failures, not forced adaptations
of this delivery; their sources are not included or edited. This report supplies
the discrepancy upward for the maintainer and the current consumer owner.

## No longer needed

None. No original imports or nodes are removed. The existing ordinary and
complex-level comparison constructions remain in use. The node previously had no
proof dependencies or numbered proof steps to prune. The new proof uses the
general flat-preservation theorem directly, without adding or proving a separate
preservation-of-all-K-flat-complexes lemma. No source-library declaration is removed
or weakened, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The concrete implementation of the two support
predicates was too expensive to compare with a generic derived-tensor proof.
The implementation refactor preserves the complete mathematical specification:
`derivedTensor` is `curriedTensor`, and `SupportTensorDescentSquare` expands to
exactly the equation written in the new generic normalization predicate.
The change record documents this for independent definition review.

The node's proof field was empty although its declaration docstring described the
intended resolution argument; it now records the argument used in Lean. The
existing generic left-derived monoidal comparison supplies the existence part
without repeating the derived bifunctor construction.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
