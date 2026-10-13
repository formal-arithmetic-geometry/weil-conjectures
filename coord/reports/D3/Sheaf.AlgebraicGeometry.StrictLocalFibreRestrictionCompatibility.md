## What changed

Proved `AlgebraicGeometry.Etale.strictLocalFibreRestriction_compatibility` with its
signature unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.StrictLocalSectionPullback`. Its proved
`strictLocal_section_pullback` supplies the restriction identity before terminal
evaluation; reassociation and cancellation of terminal evaluation finish the proof.
Updated the existing node's proof, proof_deps and proof_origin to record this route.
No definitions or existing signatures changed. Second reading removed the unused
public import `WeilConjectures.SixFunctors.BaseChange.GlobalSections`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.strictLocalFibreRestriction_compatibility`
(node `lem-sbc-strict-local-fibre-restriction-compatibility`).
No holes remain in the item, and no holes or new statements were added.
This is a proof using an existing proved theorem, not a decomposition.

## No longer needed

Removed the unused import `WeilConjectures.SixFunctors.BaseChange.GlobalSections`.
The two remaining public imports supply the statement and definition dependencies,
including `globalSectionsUpperStarMap` through the narrower upper/lower-star
global-sections module. The removed module is not used by either proof or definition.
The old proof dependency `lemma-weil-pbc-finite-pullback-composition` is unnecessary
for this proof. The direct proof dependencies
`lem-sbc-geometric-fibre-exchange-germs` and
`lem-weil-pbc-qcqs-strict-local-module-comparison` are replaced by
`lem-weil-pbc-strict-local-section-pullback`; their modules remain necessary for the
statement's definitions and are also reached by the reused theorem. No module is
claimed to leave the targets' closure. No new node is needed.

## Where the brief, the DAG or earlier work was wrong

The DAG's three-step calculation has already been implemented in the proved
`strictLocal_section_pullback` in another module. Its hypotheses match exactly,
including the pointed leg identities and both projections of i; only the final
terminal evaluation differs. Import direction checking accepts the new import.
The finite-pullback-composition node is not needed as a direct tool.
The item's unit has no realized statement or proof steps, and this reuse preserves
the existing canonical-restriction argument. The reused node is a tool from
`sk-thm-iff`; it does not replace the route of either unit.

Searches performed: msearch leanfinder on inverse-image restriction compatibility
returned Zariski restriction results, no exact Mathlib theorem; loogle found
`CategoryTheory.Iso.inv_hom_id_app_assoc`; msearch grep on global-section composition
returned no Mathlib hits. Local rg found the existing strict-local pullback theorem.
The proof of that theorem was read in full, including its terminal-evaluation,
composition-unit and pullback-projection calculations. Its source references
are Tags 03Q9 and 0A3U. The literature files named by the node are absent from this
machine, so source verification here used the existing declaration and its proof.

## Earlier second reading (a previous round; superseded)

1. Compared the only delivered Lean module with the repository using diff. Both
   existing declaration signatures and the complete data definition are byte for
   byte unchanged. Only the theorem proof/docstring and imports differ. No target,
   hypothesis, conclusion, or definition changed. Public import pruning has its
   own change record, added after the dry-run requirement.
2. Compiled the module locally through lcompile.py without errors or warnings.
   Compiled a scratch copy with `#print axioms` for strictLocalFibreRestriction,
   strictLocalFibreRestriction_compatibility, and the reused strictLocal_section_pullback.
   All three use exactly propext, Classical.choice, and Quot.sound; no sorryAx.
   Scanned the delivered Lean for sorry and forbidden declarations: none.
   Read the reused theorem's terminal-evaluation, composition-unit, and projection
   calculations in full. The final inverse/hom cancellation proves this equality.
3. No split-off statements or new nodes exist. The reused statement has exactly
   the given two projection identities and pointed-leg condition. Terminal
   evaluation cancellation is valid for every coefficient module, including zero;
   it requires no nonempty scheme or invertibility of the restriction. No data
   is chosen from an unproved existence theorem.
4. The existing proved pullback formula followed by inverse/hom cancellation is
   a short direct route. Independent rg searches for section/pullback/restriction
   compatibility found that formula and its existing use in StrictLocalExchangeCompatibility;
   msearch loogle confirmed the exact NatIso inverse/hom cancellation theorem.
   Removed the unused public BaseChange.GlobalSections import: its narrower
   defining module is already public through QcqsStrictLocalModuleComparison.
   The remaining public imports provide signature/data dependencies, and the new
   pullback import is proof-only. No longer needed lists all three former direct
   proof dependencies, distinguishing them from still-needed statement dependencies.
   Read sk-lem-universal-datum and sk-thm-iff: no realized node is bypassed; the
   canonical restriction calculation and both units' routes are preserved.
   The only importing module, IntegralFibreSectionLocalLiftAux, uses this theorem
   and compiles against the pruned module without BaseChange.GlobalSections being
   re-exported by its other imports.
5. Compared the node JSON with the repository: only proof, proof_deps, and
   proof_origin change. The two steps match the Lean application and cancellation,
   and proof_deps is exactly the union of their uses. The existing Lean record
   remains accurate; there are no new-node fields to check.

Second reading changed only the unused public import and the report's incorrect
claim that all three original imports were needed. The proof and DAG were correct
and remain as submitted. One original hole closed, zero holes added.

Import pruning change record: `coord/changes/strictLocalFibreRestriction_compatibility-import-pruning.md`.
The initial dry run required this record for the removed public re-export; added
it with all transitive users and their local claim holders.

## Second reading by D3

1. PASS. Independently diffed the delivered module against the repository and
   checked byte equality of the existing theorem signature and the entire
   strictLocalFibreRestriction data definition. Only imports, the proof docstring,
   and the theorem proof differ. The public-import removal has its change record;
   no hypothesis, conclusion, definition, or target statement changed.
2. PASS. Compiled the item through lcompile.py and compiled the scratch axiom
   probe. strictLocalFibreRestriction, strictLocalFibreRestriction_compatibility,
   and strictLocal_section_pullback use only propext, Classical.choice, Quot.sound.
   No sorry, axiom, unsafe, opaque, implemented_by, or extern occurs in the
   delivered Lean. Read the reused theorem and its private terminal-evaluation
   and composition-unit helpers: the projection calculation uses precisely ht,
   hi', and hi. The item then reassociates the equality, rewrites, and cancels
   inverse terminal evaluation with terminal evaluation.
3. PASS. No statements were split off and no nodes or holes were added. The
   already-proved arbitrary-q identity specializes with q = i, hqt = hi', hq = hi;
   it makes no additional geometric assumptions. Isomorphism cancellation is
   valid for zero modules and empty X', without any invertibility assumption on
   the restriction map. The unchanged definition constructs its map explicitly,
   rather than choosing data from an unproved existence assertion.
4. PASS. Independent rg searches for strict-local pullback/restriction formulas
   found strictLocal_section_pullback and its use in StrictLocalExchangeCompatibility.
   Upstream searches found no competing assembled formula. A fresh msearch loogle
   query found CategoryTheory.Iso.inv_hom_id_app with the exact cancellation type.
   The two public imports supply statement/data dependencies; the pullback import
   is proof-only. No longer needed covers all three former proof dependencies.
   Read the realized fields of sk-lem-universal-datum and sk-thm-iff: the first
   has no realized steps here; the latter's realized iff theorem remains intact.
   Reusing its proved tool does not bypass either unit's route. Compiled scratch
   copies of the item and IntegralFibreSectionLocalLiftAux together in import
   order: the sole direct importer compiles against the pruned module.
5. PASS. Independently checked the node diff: exactly proof, proof_deps, and
   proof_origin change. The two proof steps match the Lean application and
   terminal cancellation, and proof_deps is their uses union. The existing Lean
   record still matches the unchanged statement. No new-node fields apply.

This reading changed only the report by adding this current independent review.
The return at coord/returns/D3.md asked for two import-visibility corrections;
verified both are already present in the change record and the earlier report.
IntegralStrictHenselianGeometricFibreSections imports BaseChange.GlobalSections
privately, so it does not re-export it; the direct importer compiles without that
re-export. No further proof, import, definition, or DAG repair was necessary.
One original hole closed, zero holes added; no module is claimed pruned from the
whole targets' closure.
