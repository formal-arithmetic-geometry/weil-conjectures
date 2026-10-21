## What changed

Restored Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackSquare from the
quarantine path recorded in coord/rework.tsv. Qualified every intended derived
pullback as AlgebraicGeometry.derivedPullback to avoid the adopted source's newer
Scheme.Modules.derivedPullback. This repairs actual elaboration errors in the
archived statement and both private helpers, preserving its original mathematical
meaning, universes, binders and specified maps. Updated the node's Lean record.

The archived proof is complete: naturality is proved from the three natural
transformations defining canonicalSinglePullbackMap; equality transport is proved
by substitution; the main proof applies canonicalSinglePullbackComposition twice,
cancels only composition isomorphisms, then uses naturality for the module map a.
No single-module comparison is inverted. Both original imports remain necessary.
The existing composition dependency is already proved and was compiled unchanged
against the adopted source. Temporary unchanged source copies were removed from
the packet after compiling the sandbox dependencies.

Change record: coord/changes/E4-canonical-single-pullback-square-restoration.md.
No source-library modules, definitions, target statements or unit routes changed.

## Proved and sorry left

Zero-hole repair: the archive contained 0 sorries and the restored module contains
0 sorries. Holes closed: none. Holes added: none. Split off: none.
AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackSquare and its private
singlePullback_naturality and singlePullback_congr helpers have complete proofs.
This is restoration of an existing proof, not a new hole closure.

Validation: the restored theorem and unchanged dependencies compiled in import
order; item compile time was 44.5 seconds. A separate single-file compile took
41.5 seconds. Both runs had only the subsequently fixed line-width warning.
The final delivery repeats compilation and checks every declaration's axioms.
The two actual consumers remain quarantined with independent rework assignments;
their unchanged intended functor and theorem arguments are preserved.

## No longer needed

None. Both original imports are retained: the public comparison import supplies
the statement's canonical maps; the private composition import proves the two
square paths. Every declared proof dependency remains needed, directly or through
these imports. No node, parent dependency, module or upstream declaration is pruned.
No new node or split theorem is introduced.

## Where the brief, the DAG or earlier work was wrong

The assigned module is quarantined and already had a complete zero-hole proof;
its task is an API restoration. Unqualified derivedPullback no longer resolves
to the same functor inside Scheme.Modules after the adopted-source update.
The original compiler errors expose Type u versus Type w morphism universes.
Explicit qualification fixes this without changing the mathematics. The proof
plan and the unit's route remain correct and are retained.

The published build initially lacked the just-landed composition module's olean.
Compiling unchanged current dependency sources into the sandbox made that existing
interface available; no replacement declaration was introduced or delivered.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
