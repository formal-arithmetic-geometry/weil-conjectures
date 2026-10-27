## What changed

Filled the four theorem proofs in `Sheaf.Paper.PointRestrictionSystemChainMap`,
keeping every public statement and definition unchanged. The coefficient comparison
is assembled from the uniquely normalized finite constant-sheaf comparisons;
naturality of sheafification proves compatibility with the quotient maps.
A private explicit presentation of coefficient restriction is proved equal to the
existing functor using its uniqueness characterization. Section restrictions then
define a natural transformation of whole towers. Mathlib's
`NatTrans.mapHomologicalComplex` gives the transformation on unbounded complexes,
and componentwise extensionality proves uniqueness.

The existing DAG's four steps are retained: pointwise scalar compatibility,
coefficient-transition compatibility, strict tower naturality, and passage to
complexes with componentwise uniqueness. The node's final step now cites the concrete sequence-site API in place of the
unused general derived-calculus theorem. No definitions change.

## Proved and sorry left

Closed all four original holes, in:

- `WeilConjectures.PointRestrictionSystem.reindexContinuous`;
- `WeilConjectures.PointRestrictionSystem.coefficient_existsUnique`;
- `WeilConjectures.PointRestrictionSystem.operations_additive`;
- `WeilConjectures.PointRestrictionSystem.restriction_system_chain_map`.

All four belong to `lem-trf-point-restriction-system-chain-map`.
Zero holes remain in the item. Zero holes or split statements are added.
The proof uses existing dependency declarations; this does not assert those
imported modules are free of sorry.

## No longer needed

Removed the redundant private imports
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, and
`Sheaf.CategoryTheory.RingedSiteModules`: their required declarations are already
publicly available through the original imports. Removed the unused public imports `Sheaf.Paper.TraceFormulaCoefficientConventions`,
`Sheaf.Paper.SemilinearDerivedSections`, and `Sheaf.Paper.CoefTowerCoaugmentation`.
The remaining imports supply all declarations used by the existing signatures and
proofs. There are no current Lean importers of the item requiring adaptation.
No modules or nodes are withdrawn.

The general semilinear derived-calculus theorem is not invoked: the proof uses
the concrete ringed sequence-site presentation and Mathlib's ordinary complex
construction. The node's proof dependencies and final step now cite
`def-coef-ringed-sequence-site` instead of
`lem-coef-semilinear-derived-sections`; its obsolete tool-use entry is removed.
The latter node remains a statement dependency because the informal statement
refers to the strict-system convention.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The coefficient restriction
functor is chosen by a uniqueness characterization, so its section formulas
are not definitional. The proof establishes equality with a private explicit
presentation before using sectionwise naturality.

The retained attempt had two incomplete glue arguments: the product arrow
calculation needed explicit reduction of `sequenceVertical` followed by
`Functor.map_id`, and uniqueness needed function extensionality on complex
components and comparison with both prescribed-component proofs. Both are repaired.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
