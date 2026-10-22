## What changed

Completed the zero-hole retirement listed at coord/retire-items.tsv row 2860.
Withdraw Sheaf.AlgebraicGeometry.StrictLocalSectionPullback through deleted.txt;
attach lem-weil-pbc-strict-local-section-pullback to the existing unchanged
WeilConjectures.AlgebraicGeometry.StrictLocalSectionPullback theorem.

The twin uses the canonical full strictLocalization, whereas the retired theorem
used the small ring-colimit strictHenselizationScheme. These models are canonically
isomorphic but not definitionally equal. Preserve both direct consumer signatures
and the complete strictLocalFibreRestriction definition verbatim. Replace their
old theorem applications by the existing unitSectionRestriction_comp. Identify
the composite small-model graph with geometricFibreSectionLift by its projections:
hqt/hi', hpoint/ht and the first-projection lemma give the marked-point component;
hq/hi and the second-projection lemma give g'. Pullback extensionality closes the
graph equality. The existing exchange/colimit and terminal cancellation arguments
then finish unchanged. No renamed duplicate or new declaration is introduced.

Adapted modules: Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility and
Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility (both unclaimed
in the source snapshot). Remove their private import of the retired module and
update their nodes' proof, proof_deps and proof_origin. Public imports are preserved.
The fibre-compatibility proof paragraph now describes its actual direct argument.
Change record: coord/changes/F1-strict-local-section-pullback-retirement.md, including
the old/new theorem signatures and all 842 transitive users.

## Proved and sorry left

The assigned module had zero sorry holes before this repair. Holes closed: 0 of 0.
Holes added: 0. Split off: 0. No sorry remains in any delivered Lean file.

AlgebraicGeometry.Etale.strictLocal_exchange_compatibility
(node lem-weil-pbc-strict-local-exchange-compatibility) and
AlgebraicGeometry.Etale.strictLocalFibreRestriction_compatibility
(node lem-sbc-strict-local-fibre-restriction-compatibility) remain completely proved
with their original statements. AlgebraicGeometry.Etale.strictLocalFibreRestriction
keeps its complete concrete body. The adopted
AlgebraicGeometry.Etale.strictLocal_section_pullback is preserved in its source module.
This delivery is a retirement repair, not a new hole closure or decomposition.

Both adapted modules compile without warnings. A textual check verifies both
signatures and all public imports are unchanged, as is the data definition.
DAG proof_deps equal the union of proof-step uses in all three updated nodes.
The three immediate importers compile against the delivered set without any edit:
IntegralFibreSectionLocalLiftAux (5.1 s), QcqsGeometricExchangeFactorization (9.5 s),
and StrictHenselizationModuleFibreFactorization (14.4 s), all under Sheaf.AlgebraicGeometry.
An explicit probe importing both consumers and the adopted theorem also compiles
(2.6 s). #print axioms for strictLocal_section_pullback,
unitSectionRestriction_comp, strictLocal_exchange_compatibility,
strictLocalFibreRestriction, and strictLocalFibreRestriction_compatibility reports
only propext, Classical.choice, and Quot.sound for each, with no sorryAx.
The standalone probes initially encountered an unpublished dependency artifact;
submitting the consumers and probes together in import order resolves it through
the compile server's normal unpublished-dependency overlay.

## No longer needed

Retire lean/Sheaf/AlgebraicGeometry/StrictLocalSectionPullback.lean. Its four private
terminal/composite-unit helpers duplicate work already proved by the general
unitSectionRestriction_comp; consumers need only that general theorem and the
small-model leg projections. Remove import Sheaf.AlgebraicGeometry.StrictLocalSectionPullback
from both direct consumers. No other import is removed from surviving modules.
The withdrawn module's public imports were QcqsStrictLocalModuleComparison and
GeometricFibreExchangeGerms under WeilConjectures.AlgebraicGeometry, and
EtaleUnitSectionRestriction and SmallStrictLocalSectionMaps under
Sheaf.AlgebraicGeometry; its private import was
WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence. Those modules remain used
elsewhere; only the obsolete item module is claimed as pruned.

Both parent proof-dependency lists remove lem-weil-pbc-strict-local-section-pullback
and instead record the general composition and projection calculation. The node
itself remains attached to the existing adopted theorem. Its adopted proof does
not need def-weil-pbc-small-strict-local-section-maps or
lem-weil-pbc-etale-unit-section-restriction-comp, so those two migration-only steps
are removed from that node; both dependencies remain needed by the adapted parents.

This is an actual replacement argument in both live parents, not withdrawal based
on an importer count. The live source census and quarantine search find no other
importer or declaration use. No DAG node or quarantine archive is removed. The
sk-thm-iff realized statement/step remains unchanged, as do the units of both parents.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief did not describe this as a retirement, but the current
queue and retire-items row do. The item is already completely proved; a no-op would
not complete its assigned repair. Import replacement alone is invalid because the
twin uses another Lean presentation of the strict henselization. The direct generic
composition proof avoids changing any existing consumer scheme or theorem statement.
The DAG statement and lean.statement now record the exact adopted full-model
signature; statement_change records the old presentation and audits both parent
citers, whose unchanged conclusions remain proved by the replacement argument.
The lean.note explains why the small-model consumers are proved independently. The mathematical
representative identity is unchanged; no target statement or source-library file changes.

Read the source at literature/stacks-project/etale-cohomology.tex,
theorem-higher-direct-images (Tag 03Q9, lines 8015-8100) and
lemma-proper-base-change-f-star (Tag 0A3U, lines 18282-18309), as well as the existing
full proofs of the composition and small-model projection lemmas. The replacement
asserts only canonical restriction compatibility. No continuity, properness,
invertibility, nonempty scheme or nonzero coefficient assumption is added.

Searches made through msearch.py: leanfinder returned sheaf/module pullback composition
and global-section naturality results but no exact strict-local formula; loogle found
CategoryTheory.Limits.pullback.hom_ext; grep found that lemma and Sheaf.ΓRes_map.
Local rg found the already proved unitSectionRestriction_comp, the shortest route
needed here. No new theorem, node or definition is necessary.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
