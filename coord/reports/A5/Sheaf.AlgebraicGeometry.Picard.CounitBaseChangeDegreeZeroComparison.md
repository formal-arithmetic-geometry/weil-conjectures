## What changed

Restored the quarantined zero-hole module
Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeDegreeZeroComparison, preserving
its theorem, canonical comparison constructions, original public imports and
private mate-square import. Qualified all occurrences of derivedPullback as
AlgebraicGeometry.derivedPullback so the statement and proof retain the specified
shared HasDerivedCategory.{w} instances instead of resolving to the different
Scheme.Modules.derivedPullback.

The proof transports invertibility of R^0 f_*M to f_*M, applies the existing
single-pullback and single-direct-image invertibility lemmas, constructs a and b,
and cancels H^0 of the single-pullback comparison followed by the single-complex
homology isomorphism in canonicalDegreeZeroMateSquare. No mathematical definition
or target signature changes. The node's Lean statement and restoration note are
refreshed; its proof plan and dependencies are retained.

Change record: coord/changes/A5-counit-base-change-degree-zero-restoration.md.
Validation: lcompile.py compiled the unchanged current mate-square dependency
in 24.1 seconds and the restored item in 8.3 seconds, without warnings. Against
that same dependency, the archived item fails at lines 72 and 73 with the
DerivedCategory universe/type mismatch described above. The unchanged dependency
was compiled only for validation and is not included in the delivery.

The sole actual consumer found across lean/ and quarantine/ is the separately
quarantined CounitBaseChangeIsIso, whose existing application retains its intended
type and needs no adaptation. The unit route is retained.

## Proved and sorry left

The delivered declaration is
AlgebraicGeometry.Scheme.Modules.counitBaseChange_degreeZero_comparison
(node lem-pc-counit-base-change-degree-zero-comparison).

This is an assigned restoration repair with zero holes in the preserved source:
0 holes closed, 0 holes added, 0 split off, and 0 remaining in the delivered module.
The existing complete proof is restored against the adopted interfaces. Imported
theorems are used through their existing declarations; no new theorem or axiom
is introduced.

## No longer needed

None. Both original public imports and the private
Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare import remain.
All three direct proof dependencies remain needed:
lem-pc-canonical-single-pullback-comparison supplies the two pullback isomorphisms;
lem-pc-canonical-single-direct-image-comparison supplies the acyclic image
isomorphism; lem-pc-canonical-degree-zero-mate-square supplies the compatibility
identity and H^0 direct-image comparison. No node, declaration or module is
withdrawn, and none is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned source is quarantined, not withdrawn; its zero-hole proof and Lean
attachment must be restored. The older unqualified derivedPullback references
collide with the adopted Scheme.Modules.derivedPullback. The qualification repair
retains the original mathematical statement and shared derived-category choices,
as already done for its mate-square and single-pullback dependencies.

The shorter-route searches found generic mate and cancellation identities, while
the existing complete proof already uses the precise comparison square. There
is no reason to create another split or change the recorded route.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
