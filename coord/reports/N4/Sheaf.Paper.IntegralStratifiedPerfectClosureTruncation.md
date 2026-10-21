## What changed

Proved truncation and cohomology closure directly in
`AlgebraicGeometry.Scheme.integralStratifiedPerfectClosure`, in module
`Sheaf.Paper.IntegralStratifiedPerfectCharacterization`, from the existing
`integralStratifiedPerfectCharacterization` equivalence. Local finite-presentation models
are invariant under isomorphism by composing their realization isomorphisms. Vanishing
cohomology above the upper bound supplies the zero case. The proved source-library
homology-property truncation lemmas and the standard truncation bounds give both truncated
objects. A cohomology sheaf placed in degree zero has bounds [0,0], the given permitted
sheaf there, and zeros elsewhere. Applying the reverse characterization completes both
clauses. No truncation is commuted with non-flat coefficient reduction.

Withdrew the assigned standalone split. The newly landed N3 homology theorem is preserved
with its existing signature and proof structure: only its private import and two calls
are migrated to the parent's truncation clause. Removing the parent's homology import
and directly proving its cohomology clause avoids an import cycle. The parent privately
imports HomologyProperty. DAG routes match these exact dependencies. Change record:
`coord/changes/N4-integral-closure-pruning.md`.

Repaired the return at head 5052ddcc9: the change record now explicitly names
`Sheaf.Paper.IntegralStratifiedPerfectCharacterization` and its holder K2. The retained
Lean changes match the current shared source outside the necessary adaptations.

The parent compiles in 7.9 seconds, the adapted homology module in 3.9 seconds, through
lcompile.py. The generic formulas cover cutoffs outside [a,b], zero K and empty T.

## Proved and sorry left

Assigned module: one original hole, zero retained holes; removed by pruning, not counted
as a direct proof of the removed declaration. The removed hole is
`AlgebraicGeometry.Scheme.integralStratifiedPerfectClosure_truncation`
(`lem-weil-pbc-integral-stratified-perfect-closure-truncation`). No holes added, no result
split off. Both parent closure branches have complete replacement proofs from the
already-stated characterization.

The adapted parent retains its two pre-existing holes unchanged:

- `AlgebraicGeometry.Scheme.integralStratifiedPerfectCharacterization`
  (`lem-weil-pbc-integral-stratified-perfect-characterization`).
- `AlgebraicGeometry.Scheme.integralStratifiedPerfectDetailed` (the same parent node).

The adapted `AlgebraicGeometry.Scheme.integralStratifiedPerfectClosure_homology` has
zero holes: N3's proof already landed without holes, and its proof is preserved except
for the two forced call migrations. This delivery does not claim credit for N3's closure.

## No longer needed

Removed standalone declaration, module and incoming dependencies:
`Sheaf.Paper.IntegralStratifiedPerfectClosureTruncation`, declaration
`AlgebraicGeometry.Scheme.integralStratifiedPerfectClosure_truncation`, node
`lem-weil-pbc-integral-stratified-perfect-closure-truncation`. Its file is listed in
deleted.txt, and its node remains with a null Lean attachment.

Removed private imports of the item from both adapted modules. Removed the parent's
private import of `Sheaf.Paper.IntegralStratifiedPerfectClosureHomology` and its DAG
dependency on `lem-weil-pbc-integral-stratified-perfect-closure-homology`: that module's
proved public theorem is retained, with its two truncation calls redirected to the
parent. The parent itself now needs neither split. The homology module no longer needs
the standalone truncation split. Its own source and node remain in the library.

Searches of current and quarantined sources, DAG dependencies, proof-step uses and unit
realizations identify precisely these two current consumers of the item. Both have the
replacement arguments and dependency changes in this same delivery. The item does not
realize a unit statement or step. Uniform-complete triangulation remains needed for
shifts and cones; none of its dependencies is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

Closure under shifts and cones alone does not imply closure under standard truncations.
The truncation node's sole listed dependency is insufficient. The parent already states
the stronger cohomological characterization before the closure theorem, and its docstring
already gives the correct route. The split duplicated a consequence of that equivalence.
No target statement or definition repair is needed.

## Forced adaptations

`Sheaf.Paper.IntegralStratifiedPerfectCharacterization` is held by K2, as identified
in the return; its earlier A3 claim is historical. This holder is named in the change
record. `Sheaf.Paper.IntegralStratifiedPerfectClosureHomology` was held by N3 during
the session and its proof has landed. The packet preserves every existing signature
and visibility of both modules and changes only the necessary proof/import lines.

With the item compiled empty, the original characterization module fails at its call:

```text
IntegralStratifiedPerfectCharacterization.lean:420:10: error(lean.unknownIdentifier):
Unknown identifier `integralStratifiedPerfectClosure_truncation`
```

The current N3 homology source also imports the withdrawn item and calls that declaration
twice. Its original fails against the empty item, whereas the adapted module compiles.
The original compiler errors are:

```text
IntegralStratifiedPerfectClosureHomology.lean:46:5: error(lean.unknownIdentifier):
Unknown identifier `integralStratifiedPerfectClosure_truncation`
IntegralStratifiedPerfectClosureHomology.lean:48:5: error(lean.unknownIdentifier):
Unknown identifier `integralStratifiedPerfectClosure_truncation`
```

Only that import and the two calls change: they use the parent closure theorem's
truncation clause with identical arguments and conclusions. All remaining N3 proof lines,
including the shifted-heart identification, remain verbatim.

This import migration forces the characterization module to remove its homology import
and directly prove its final cohomology clause, so the new imports stay acyclic. The new
truncation and cohomology arguments share the same local property Q and existing
characterization. Existing definitions, signatures, visibility, docstrings and public
imports are unchanged. Both adaptations compile with zero new holes.

## Forced adaptations

### Sheaf.Paper.IntegralStratifiedPerfectCharacterization
Original imports module(s) explicitly withdrawn in deleted.txt: Sheaf.Paper.IntegralStratifiedPerfectClosureTruncation. Those imports must be migrated in this delivery; the baseline's compiled copies are not valid counterfactual dependencies. Adapted module compiled in the delivered set. CODEX verifies the migration and every accompanying API adaptation is needed.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
