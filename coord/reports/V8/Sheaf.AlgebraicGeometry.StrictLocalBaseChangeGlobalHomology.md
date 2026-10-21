## What changed

Restored the quarantined `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology`
with its original small-model statement and complete colimit proof. Replaced the now-empty
public `StrictHenselizationRestriction` import with the actual current statement providers:
`Mathlib.CategoryTheory.Sites.GlobalSections`,
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap` and
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`.
Kept just the private presentation and derived-continuity imports needed by the proof.
Every byte from the module docstring onward agrees with the preserved quarantine source.
No source-library file, definition, target, consumer or quarantine archive changes.
Change record: `coord/changes/V8-strict-local-global-homology-restoration.md`.

The original presentation supplies a colimit source cocone. Derived continuity proves its
extension along the global homology mate is also colimiting. Cocone uniqueness identifies
the colimit comparison with that mate, proving its invertibility. The existing DAG already
records exactly this route and both used proof dependencies, and needs no edit.

## Proved and sorry left

Zero-hole restoration repair. The archive has 0 textual holes; the repaired item has 0.
Holes closed: 0. Holes added: 0. Split off: 0. No `sorry` remains in the delivery.
The restored theorem is
`AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_globalHomology`
(node `lem-weil-pbc-strict-local-base-change-global-homology`).
Validation: the restored module compiles in 5.3 seconds, and an importer applying
the theorem at the exact archived signature compiles in 3.1 seconds. `#print axioms`
reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Both compiles are clean.
Import-direction checks permit both proof imports without a cycle.
Its signature and complete proof are preserved, including every integer degree,
arbitrary bounded-below abelian coefficients and the original strict-local model.

## No longer needed

Removed obsolete or redundant imports from this file:

- `Sheaf.AlgebraicGeometry.StrictHenselizationRestriction` (withdrawn public shim);
- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`;
- `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`;
- `Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit`;
- `Sheaf.AlgebraicGeometry.StrictHenselization`;
- `Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

The presentation proof already supplies its own necessary geometry and germ dependencies.
The statement providers expose the upper/lower-star and strict-local definitions directly.
No mathematical node or module is claimed globally pruned; no dependency of the retained
presentation or adopted source theorem is removed. Both existing proof-dependency edges
are retained. All parents, including the three quarantined direct importers, remain valid
at their original theorem applications; their independent restoration work is preserved.

## Where the brief, the DAG or earlier work was wrong

This is a quarantined restoration repair with zero holes, rather than an unproved theorem.
Compiling the archived file fails because `StrictHenselizationRestriction` is now empty:
`Scheme`, `Quiver.Hom` and `QuasiCompact` are unavailable in its public statement.
The replacement public imports repair that defect while preserving the exact theorem.
The archived dependency imports also refer to retired twins and are unnecessary for
this proof. The adopted global-homology theorem uses `strictLocalization` instead of
`strictHenselizationScheme`; replacing the assigned theorem by that signature would
change the small-model interface, so it is not used as a replacement.

Read the source Stacks `etale-cohomology.tex`, theorem-higher-direct-images (03Q9),
and lemma-colimit-complexes (0GIT). The bounded-below continuity assertion and canonical
restriction map are exactly those assembled by the preserved proof. The unit record
`sk-prop-h2` has empty realized lists; no unit statement or route is changed.
LeanFinder and Loogle found the Mathlib colimit-uniqueness/isomorphism criterion already
used in the proof. Repository search found the canonical-model counterpart and the
restored original-model presentation. No new mathematical result or split is needed.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
