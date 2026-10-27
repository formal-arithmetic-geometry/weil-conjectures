## What changed

Retire the assigned declaration-free module
Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula through deleted.txt.
The current retirement manifest lists this item, while the proof brief and
experimental ROUTE paths describe an earlier state. The canonical theorem
AlgebraicGeometry.Etale.rawModuleScalar_source_class_formula is already fully
proved in WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceClassFormula.
Its statement, complete proof and imports are preserved verbatim.

Append a retirement note to the node's existing canonical upstream Lean record.
No other node field changes. No Lean consumer needs adaptation: live and
quarantined sources have no importer of the assigned Sheaf path, and its
historical consumer has already been withdrawn. The actual mathematical parent
imports the canonical upstream theorem directly and retains its DAG dependency.

Change record:
coord/changes/Y7-retire-raw-module-scalar-source-class-formula.md.

## Proved and sorry left

The current assigned module has zero declarations and zero sorries. Holes
closed: 0. Holes added: 0. Holes left in the assigned module: 0. No new theorem
or decomposition is introduced; this delivery completes its listed retirement.

The existing theorem AlgebraicGeometry.Etale.rawModuleScalar_source_class_formula
and its mathematical parent
AlgebraicGeometry.Etale.rawModuleAbelianHomMap_source_formula retain their
complete canonical proofs. Optional full single-file recompilation of the unchanged upstream proof and
its unchanged parent each reached the 60-second limit. These scratch checks
are outside the delivery; no proof, definition or consumer is changed here.
The delivery tool independently validates the pure withdrawal and its import
closure. The import-only probe CanonicalAxiomCheck.lean compiled successfully in
7.3 seconds. Both rawModuleScalar_source_class_formula and
rawModuleAbelianHomMap_source_formula use exactly propext, Classical.choice
and Quot.sound, with no sorry dependency. Its complete output is in scratch
evidence via the fixed compile-result file.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula.
Remove its four public reexport edges by withdrawing the unused shim:
WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceClassFormula,
WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted,
Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix and
Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso. These modules are
not themselves withdrawn in this delivery. Their canonical declarations and
all uses from other modules remain available.

No mathematical node is pruned. In particular,
lem-sbc-raw-module-scalar-source-class-formula and the parent's dependency on
it remain. The unit sk-lem-failure-field and its realized route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The brief's source-square repair and supplied experimental paths predate the
current source. Those experiment directories are absent here. The current
assigned file is a zero-hole shim; the theorem node already names its proved
upstream declaration. The concrete Sheaf source-square and unshifted-coefficient
modules are already empty withdrawals. Reconstructing those modules or adding
a duplicate theorem would undo the canonical migration.

The historical retirement manifest lists one Sheaf consumer. That consumer is
already withdrawn by G2, and its canonical upstream replacement already imports
and applies the canonical source-class theorem. Both downstream.py and a full
Lean/quarantine source scan now report zero importers of the shim.

LeanFinder, Loogle and Mathlib grep searches were repeated through msearch.py.
They confirm the generic inverse-naturality API; local source search finds the
complete canonical source-square/naturality proof already used here. No new
lemma, source, hypothesis, target statement or mathematical route is required.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
