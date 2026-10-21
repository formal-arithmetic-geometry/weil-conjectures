## What changed

Restored Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit from the
quarantine source named by coord/rework.tsv. Removed only `derivedPullback` from
the local irreducibility attribute command: its current `irreducible_def` already
sets that status, and Lean rejects setting it again. The original fails at line
28 with that diagnostic; the repaired file compiles cleanly through lcompile.py
in 22.0 seconds.

The declaration AlgebraicGeometry.derivedPullbackComposition_mate_unit, both
private proved helpers, all imports and documentation remain verbatim. The proof
transposes the comparison-counit normalization using conjugateEquiv_counit and
naturality, then applies derivedDirectImage_pasted_counit_normalization. Both
declared dependencies have been read and remain used. The canonical comparison
in the first normalization unfolds to the same fixed choice used in this theorem.
The node's Lean attachment, proof and proof_deps already describe this argument;
no node update or new mathematical statement is needed. The unit route is preserved.

Change record: coord/changes/N4-derived-pullback-composition-mate-restoration.md.
The source and consumer checks are documented there. No consumer adaptation is
forced by this local command repair.

## Proved and sorry left

This is a zero-hole rework assignment. Restored the complete proof of
AlgebraicGeometry.derivedPullbackComposition_mate_unit
(node lem-sc-derived-pullback-composition-mate-unit). It has zero direct sorries
before and after the repair. Holes closed: 0. Holes added: 0. Sorries left in the
item: none. No statements are split off. The two private mate lemmas remain proved.

## No longer needed

None. No import, declaration, node or module is pruned. Both counit-normalization
proof imports and the public GlobalHomAdjunctionIso import are preserved. The
quarantine archive remains untouched. Although there are no current Lean imports
of this Sheaf path, the parent DAG node still cites it; it is not withdrawn.

Searches through msearch.py used Loogle for conjugateEquiv, LeanFinder for the
mate-unit equation, and grep for conjugateEquiv_counit. These found generic
categorical mate identities. The adopted source twin already has the same local
attribute correction, but the retirement census explicitly retains this Sheaf
module because the upstream twin reaches other retained upstream copies.

## Where the brief, the DAG or earlier work was wrong

The archived local attribute command predates derivedPullback becoming an
irreducible_def. Removing its redundant entry repairs the actual compiler failure.
There is no mathematical statement or proof-plan error. The broad proving brief's
expectation of sorries does not apply to this quarantined zero-hole repair.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
