## What changed

Restored `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperStarUnitCoherence.lean`
from the exact quarantine path recorded in `coord/rework.tsv`. The live source was absent
following the cluster-restore rollback of 2026-10-20. The delivered file is byte-identical to
the archive: all fourteen theorem proofs, the concrete definition
`CategoryTheory.Functor.mapHomotopyCategorySingleHom`, the three public imports, signatures,
visibility, attributes and private helpers are preserved. The quarantine archive is untouched.

The restored file compiles cleanly through `lcompile.py` against the published library
(40.1 seconds). Its proof route is unchanged: the homotopy-category single-object calculations
transport the existing underived identity/composition unit equalities through the derived
counit comparison lemmas; the full subcategory forgetful map gives bounded-constructible
coherence, and conjugacy of adjunctions gives the pushforward identity at the unit.

The change record is `coord/changes/H1-derived-upper-star-unit-coherence-restoration.md`.

The unchanged direct consumer `WeilConjectures.TraceFormula.Slop.Dualizing` also compiles
against the restored source in a separate scratch sandbox (25.4 seconds; the restored
dependency took 42.0 seconds). Its existing duplicate-namespace linter warning at line 296
is unrelated to this repair. No consumer adaptation is required.

## Proved and sorry left

This is a zero-hole restoration repair, not a new proof or decomposition. The archived
module has zero `sorry`s; the restored module has zero `sorry`s. Holes closed: none (0 of 0).
Holes added: none. Split-off statements: none. Every archived proof is retained, including
`leftDerivedUpperStarId_hom_app_unit`, `leftDerivedUpperStarComp_hom_app_unit`,
`boundedConstructibleUpperStarId_hom_app_unit`,
`boundedConstructibleUpperStarComp_hom_app_unit`, and
`boundedConstructibleLowerStarId_inv_app_unit` in
`AlgebraicGeometry.ProEtale.CondensedRing`.

## No longer needed

None. No import, declaration, node, module or dependency is withdrawn. In particular the
three archived public imports remain verbatim. No DAG attachment to this module or its
declarations was found in `dag/nodes/`, and no DAG route or unit realization is changed.

## Where the brief, the DAG or earlier work was wrong

The item is an explicitly listed rework restoration with no proof holes, rather than a
module whose theorem still needs proving. Its absence from `lean/` did not mean withdrawal:
the preserved source is in `quarantine/`, as the rework row says. There is no current return
for this item in `coord/returns/H1.md`.

The normal downstream tool reports an unknown module because the live source is absent.
Searching both live roots and quarantine finds the live direct importer
`WeilConjectures.TraceFormula.Slop.Dualizing`, whose `BorelMooreSection.integral_point` uses
`boundedConstructibleLowerStarId_inv_app_unit`. That consumer is preserved unchanged.
The earlier D3 geometric-instance repair is already present in the archived private
helper's omit clause and is preserved; no additional interface correction is needed.

Searches were run with the supplied `msearch.py`: LeanFinder returned generic pullback
coherence results, Loogle did not recognize `Functor.Monoidal.εIso`, and grep found no
Mathlib copy of the restored specialized declarations. Local source searches found the
existing underived unit-coherence and derived-counit lemmas used by the archived proof.
There is no reason to replace this complete argument or duplicate it in new statements.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
