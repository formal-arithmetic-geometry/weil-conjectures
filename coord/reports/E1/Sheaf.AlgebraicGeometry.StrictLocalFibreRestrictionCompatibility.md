## What changed

Completed the zero-hole retirement listed in coord/retire-items.tsv row 2901.
Withdraw lean/Sheaf/AlgebraicGeometry/StrictLocalFibreRestrictionCompatibility.lean
through deleted.txt. Reattach lem-sbc-strict-local-fibre-restriction-compatibility
to the existing unchanged adopted declarations in
WeilConjectures.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility.

The adopted strictLocalFibreRestriction and compatibility theorem use the canonical
full strictLocalization model. The retired version uses the small ring-colimit
strictHenselizationScheme. These models are canonically isomorphic but not
definitionally equal, so import substitution cannot preserve the sole consumer.

Adapt Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux (unclaimed in the
current claim census). Remove its private import of the retired module. Keep its
theorem signature, visibility, docstring and every public import verbatim.
Construct the same section restriction as a concrete proof-local let r, prove it
invertible from its factors, and take asIso r. For each small-model limit leg apply
unitSectionRestriction_comp. Identify the resulting graph with
geometricFibreSectionLift by the two pullback projections, using hi', hpoint j and
the small-model first projection for the marked-point component, and hi and the
second projection for the other component. Expand unitSectionRestriction and
cancel terminal evaluation. No replacement public declaration or new lemma is added.

Update the two affected nodes' proof, proof_deps and proof_origin. The retired
node's statement and lean.statement now record the exact adopted signature, with
a statement_change explaining the model migration and auditing its sole DAG citer.
The consumer node records the complete replacement argument and removes the obsolete
small-model compatibility dependency. Neither the unit nor chapter route changes.

Change record: coord/changes/E1-strict-local-fibre-restriction-retirement.md.
No source-library file, target statement or quarantine archive changes.

## Proved and sorry left

This is an assigned zero-hole retirement, not a new hole closure or decomposition.
Holes closed: 0 of 0. Holes added: 0. Split off: 0. No sorry remains in any delivered
Lean file.

AlgebraicGeometry.Etale.exists_integralStrictLocalFibreComparison
(node lem-sbc-integral-strict-local-fibre-comparison) remains completely proved with
its original statement. AlgebraicGeometry.Etale.strictLocalFibreRestriction and
AlgebraicGeometry.Etale.strictLocalFibreRestriction_compatibility remain in their
unchanged adopted source module; the duplicate small-model declarations are retired.

The adapted consumer compiles without warnings in 8.0 seconds. Textual checks verify
its entire original signature, docstring and public imports, and verify that both
updated nodes' proof_deps equal the union of their proof-step uses. The source and
quarantine census finds exactly one retired-module consumer and no remaining importer
after the adaptation. There is no current Lean importer of the adapted consumer.
A separate compile and axiom audit checks the actual adapted proof body, and another
probe imports it together with the adopted compatibility module to check coexistence.
Both compile without warnings (9.7 and 2.2 seconds). #print axioms for the adapted
exists_integralStrictLocalFibreComparison, adopted strictLocalFibreRestriction,
adopted strictLocalFibreRestriction_compatibility and unitSectionRestriction_comp
reports only propext, Classical.choice and Quot.sound for each, with no sorryAx.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility.
Remove import Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility from
Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux. Its concrete restriction
construction is now local to that proof, and the compatibility calculation follows
from the already proved general unit composition theorem and leg projections.
No other import is removed from a surviving module.

The retired module's public imports were
WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms,
WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison,
Sheaf.AlgebraicGeometry.EtaleUnitSectionRestriction and
Sheaf.AlgebraicGeometry.SmallStrictLocalSectionMaps. All remain in use elsewhere;
none is claimed as pruned.

The consumer proof no longer uses the small-model specialization represented by
lem-sbc-strict-local-fibre-restriction-compatibility, so remove that dependency and
record its actual general composition/projection calculation. The compatibility
node itself remains attached to the adopted full-model theorem, whose unchanged
proof uses lem-weil-pbc-strict-local-section-pullback. Its former small-model
proof dependencies lem-weil-pbc-etale-unit-section-restriction-comp and
def-weil-pbc-small-strict-local-section-maps remain necessary in the adapted consumer;
lem-sbc-geometric-fibre-exchange-germs remains necessary for the fibre definitions.
No DAG node or unit realization is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief did not state the retirement explicitly, but the current
queue and retire-items row identify this as a retirement assignment. The item is
already completely proved, so a no-op would not complete the assigned repair.
The adopted and small-model statements cannot be interchanged definitionally.
The explicit consumer construction and direct graph calculation preserve the old
small-model conclusion while allowing the duplicate declaration to be withdrawn.
The only current DAG citer is lem-sbc-integral-strict-local-fibre-comparison; its
exact statement is retained and its new argument is delivered in the same packet.

Read literature/stacks-project/etale-cohomology.tex, theorem-higher-direct-images
(Tag 03Q9, lines 8015-8100) and lemma-proper-base-change-f-star
(Tag 0A3U, lines 18282-18309), and the complete existing general composition and
small-model projection proofs. The graph calculation uses no nonempty-scheme or
nonzero-coefficient hypothesis. It preserves the existing integral restriction
argument; no properness, continuity or invertibility assertion is added to the
compatibility calculation.

Searches through msearch.py: leanfinder returned eight scheme structure-sheaf and
Spec restriction formulas, with no matching etale section formula; loogle returned
CategoryTheory.Limits.pullback.hom_ext; grep found no Mathlib match for the general
unit-section composition names. Local rg found unitSectionRestriction_comp and
the two small-model projection formulas, the existing route used here. The adopted
compatibility theorem is preserved unchanged, rather than introducing a duplicate
under a new name. No new nodes, axioms or unfinished results are introduced.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
