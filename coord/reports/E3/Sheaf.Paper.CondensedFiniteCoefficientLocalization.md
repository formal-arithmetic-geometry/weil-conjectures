## What changed

Restored Sheaf.Paper.CondensedFiniteCoefficientLocalization from the archive named in
coord/rework.tsv. Preserved its public theorem, finite coefficient objects, imports,
DAG attachment, and source-based localization argument. Unpacked the dependent recollement
instance separately in pushScalarSingleIso and localizationTriangle.

Change record: coord/changes/E3-restore-condensed-finite-coefficient-localization.md.

## Proved and sorry left

This is a zero-hole restoration/repair. The archive contains zero sorry proofs; no hole
is closed or added. AlgebraicGeometry.ProEtale.exists_finiteCoefficient_localization_triangle
and all private helpers retain complete proofs. No statements are split off.
Node: lem-weil-pbc-condensed-finite-coefficient-localization.

## No longer needed

None. All three declared proof dependencies remain used: condensed open/closed recollement,
abelian closed support, and the normalized module-forgetful pullback comparison.
No node, module, or import is withdrawn. The archived gluing parent still needs this theorem.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined zero-hole restoration, rather than a fresh proof-hole item.
Initial compilation reported a generalization error and then a kernel argument mismatch in
Mod.monoidalClosed when using the published recollement artifact. Recompiling the unchanged
CondensedOpenClosedRecollement source (42.8 seconds) and then this item (9.9 seconds)
succeeded. This dependency was compiled only for diagnosis and is not changed or delivered.
The restored item uses named hypotheses to separate its dependent instance witness.
The mathematical theorem and DAG route remain unchanged.
Search found the Mathlib single/homology comparison already used by the proof, but no
replacement for the geometric localization and coefficient comparisons.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
