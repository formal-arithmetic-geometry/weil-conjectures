## What changed

Restored Sheaf.Paper.AdicSuppliedModelFlatCriterion from its recorded quarantine source.
Repaired the obsolete LocallyClosedStratification T quantifier to use the current
AlgebraicGeometry.Scheme.Stratification T. No mathematical hypothesis or conclusion
changes: on the assumed Noetherian T, locally closed strata are constructible, as
implemented by Stratification.ofNoetherianSpace. Updated only lean.statement in the
existing node to match. All imports, the proof plan and dependencies are preserved.
The original file fails with an unknown identifier; the repaired full module compiles
cleanly through lcompile.py in 4.4 seconds without any resource-limit change.

Change record: coord/changes/J2-adic-supplied-model-stratification-rework.md.
This packet completes the assigned rework restoration, not the theorem's proof.

## Proved and sorry left

Closed: 0 holes. Added: 0 holes. Split off: 0 statements.
The single pre-existing sorry remains in
AlgebraicGeometry.Scheme.pbc_adic_flat_iff_supplied_model_flat
(node lem-weil-pbc-adic-flat-iff-supplied-model-flat).
Its source and complete natural-language argument remain in the original docstring
and DAG proof. No data construction or definition contains a sorry in this module.

## No longer needed

None. No imports, declarations, nodes, modules, proof dependencies or unit steps are
pruned. The quarantined parent Sheaf.Paper.AdicTorFlatCohomology still uses this
criterion and retains its attachment and dependencies.

## Where the brief, the DAG or earlier work was wrong

The item is missing from lean/ because it is quarantined, not because it was withdrawn.
The preserved source and node's recorded Lean signature used LocallyClosedStratification,
an identifier the current adopted library no longer exposes. Scheme.Stratification is
the current finite constructible locally closed stratification interface. The existing
Noetherian hypothesis makes this a presentation repair, including the empty cases.
The only archived consumer already contains the same obsolete name; it has no live
compiling module to adapt, and its separate rework must repair that occurrence.
The mathematical criterion and its proof obligation have not been weakened or moved.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
