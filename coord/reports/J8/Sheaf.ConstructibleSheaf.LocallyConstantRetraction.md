## What changed

Completed the explicit retirement assignment in coord/retire-items.tsv (row for
Sheaf.ConstructibleSheaf.LocallyConstantRetraction). Withdrew the duplicate module via
deleted.txt and reattached split-locally-constant-retraction to the existing theorem
AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_retraction
in WeilConjectures.ConstructibleSheaf.LocallyConstantRetraction.

The upstream theorem differs only by dropping the unused `_sheaf` name suffix.
An exact application of it at the copy's complete original signature compiled in
2.8 seconds. `#print axioms` reports only propext, Classical.choice and Quot.sound.
The unchanged parent LocallyConstantReduction also compiled cleanly in 5.2 seconds.
The mathematical source is Stacks etale-cohomology.tex, section-trace-method,
definition-trace-map and the immediately following restriction/trace degree formula
(lines 10330–10385), read against the existing upstream proof.

Change record: coord/changes/LocallyConstantRetractionRetirement.md.

## Proved and sorry left

Zero existing holes; zero holes closed; zero holes added; zero holes left.
This is a duplicate-module retirement, not a newly closed proof. The retained upstream
theorem exists_finite_etale_retraction is already proved with only the permitted axioms.
No intermediate theorem was split off. The comparison checks every original hypothesis
and the unchanged conclusion, so in particular preserves the degree-one and zero-sheaf
cases; degree zero is excluded by the unchanged nondivisibility hypothesis.

## No longer needed

Pruned module: Sheaf.ConstructibleSheaf.LocallyConstantRetraction, including its unused
name exists_finite_etale_retraction_sheaf. No current or quarantined Lean module imports
it or calls that name. No consumer imports therefore need editing.

The removed copy's imports were WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber,
WeilConjectures.ConstructibleSheaf.Defs,
WeilConjectures.AlgebraicGeometry.FiniteEtaleModuleTraceDegree, and
Mathlib.Algebra.Field.ZMod. These modules remain needed by the retained upstream proof;
none is claimed as pruned. No DAG node or proof dependency is pruned: the parent's
split-locally-constant-retraction dependency remains realized by the official theorem.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes an open proof, but the current assignment is explicitly
listed as a retirement and already contains no sorry. Its listed API difference is only
the `_sheaf` suffix, not a difference in mathematical statements. The DAG still pointed
to the obsolete copy although its parent
WeilConjectures.ConstructibleSheaf.LocallyConstantReduction already imports and applies
the official theorem. Reattaching the node repairs that mismatch without changing
any statement, the unit route or any source-library file.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
