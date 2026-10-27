## What changed

Restored `lean/Sheaf/Paper/DerivedOpenRestrictionSuccessive.lean` from the exact archive
named by its current `coord/rework.tsv` row. The live Lean path was absent, not withdrawn.
The restoration reinstates `AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenRestrictionSuccessive`
and its complete private proof, preserving all statement binders and the existing public import.

The proof lifts ordinary module-pullback associativity to exact derived pullback,
uses three associativity equations to establish horizontal square pasting, and takes
mates to obtain successive derived open restriction. All helpers are proved.
Removed the redundant explicit proof import
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`: the retained module-pullback
coherence import already publicly imports it. No shared definitions, signatures,
attributes, DAG dependencies, or other existing modules were changed.

## Proved and sorry left

This is a quarantine restoration with zero initial holes, not a newly closed proof.
The archived proof of
`AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenRestrictionSuccessive`
(node `lem-sfb-derived-open-restriction-successive`) is retained in full.
Holes closed: zero of zero. Holes added: zero. Holes remaining: zero.
No split-off statements were introduced.

The restored archive compiled through `lcompile.py` against the current server library
in 17.2 seconds with no errors or warnings. The final version, after removal of the redundant
proof import, compiled in 19.1 seconds with no errors or warnings. The delivery tool performs its own
compilation, axiom probe, and preflight checks.

## No longer needed

Removed one redundant direct import:
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`.
Its declarations, including mate whiskering, remain needed and are provided by the
retained public imports of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence`.
No mathematical dependency node or module is pruned or withdrawn in this repair.
The current DAG already matches the retained proof.

## Where the brief, the DAG or earlier work was wrong

The assignment is a build-rework restoration rather than a module containing a current
`sorry`: its archive already contains a complete proof. The archived file compiled
unchanged against the current library, so the earlier global-build failure did not
reproduce. This delivery restores the missing theorem rather than substituting an empty
module, deleting its archive, or moving its mathematical obligation elsewhere.
The proof needs only commutative squares, but the theorem retains every assigned
pullback and open-immersion hypothesis. The formal mate argument includes identity
maps and empty opens. No unit route or canonical comparison construction changes.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
