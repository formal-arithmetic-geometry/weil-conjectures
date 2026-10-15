## What changed

Repaired `Sheaf.AlgebraicGeometry.ProEtaleRingedLocalizationSequence` by removing the
four private extension-by-zero helper declarations duplicated by
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`. The open-section counit proof now
uses the existing generic `overPushforwardOverAdj` adjunction and the adjoint-triple
criterion; the theorem signature and all geometric localization code are unchanged.
Added the proof-only `Mathlib.CategoryTheory.Adjunction.Triple` import required for that
criterion.

## Proved and sorry left

`AlgebraicGeometry.Scheme.proEtale_ringed_localization_sequence` remains proved.
The two previously delivered helper modules remain fully proved:
`SheafOfModules.inverseImage_underlying_unit_of_ring_presentation` and
`AlgebraicGeometry.Scheme.proEtale_module_unit_bijective_of_specialization`.
Closed the original hole `AlgebraicGeometry.Scheme.proEtale_ringed_localization_sequence`
(1 of 1 original holes). Added holes: none; split-off holes: none. The two new helper
theorems above are proved, not deferred statements. No `sorry` is present in the
delivered files. All three public theorems pass `#print axioms` with exactly
`propext`, `Classical.choice`, and `Quot.sound`; in particular there is no `sorryAx`.

## No longer needed

The duplicated private declarations `SheafOfModules.extensionRestrict_of`,
`SheafOfModules.extensionPresheafHomEquiv_naturality_right`,
`SheafOfModules.extensionPresheafHomEquiv_naturality_left_symm`, and
`SheafOfModules.extensionSheafAdjunction_unit_isIso` were removed from this module;
their local construction is no longer needed here.

Removed direct imports: `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison`,
`Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover`,
`Sheaf.RingTheory.IndEtaleStability`,
`Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections`,
`Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying`,
`Sheaf.CategoryTheory.SiteCoveringAxioms`,
`Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, and
`Sheaf.CategoryTheory.RingedSiteModules`. The specialization-restriction module
remains needed through the new specialization-unit helper.

Removed from the item node's direct `proof_deps`: `def-weil-pbc-proetale-site`,
`def-weil-sheaf-of-modules-category`, `def-weil-pbc-sites-and-cohomology`,
`def-weil-size-convention`, `lem-weil-pbc-ind-etale-stability`,
`lem-weil-pbc-proetale-affine-wcontractible-covering-family`,
`lem-weil-pbc-proetale-module-inverse-image-underlying`,
`lem-weil-pbc-proetale-ringed-open-comparison`,
`lem-weil-pbc-proetale-specialization-restriction-sections`,
`lem-weil-pbc-qcqs-morphism-permanence`, and
`lem-weil-pbc-spec-localization-away-basic-open`. The specialization-restriction
node is still used by the new helper. The site and module-category definition
nodes remain statement dependencies, but their recorded wrapper declarations
`proEtaleDerivedCategory` and `ringedSiteModules` are not used in this proof; their
modules must not be reintroduced as proof imports. The remaining replaced steps use Mathlib
affine covers, compact-open classification, quasi-compact pullbacks, and the
existing closed-localization and ring-splitting results. No node is deleted, and
no whole-module closure pruning is claimed without the ledger computation.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery restated private extension-by-zero lemmas already present in the
open-closed module, which the import-pruning checker rejects even though the names are
private. Reusing the generic restriction/direct-image adjunction avoids that duplicate
while preserving the same sectionwise bijectivity conclusion and avoids an import cycle.

## Earlier second reading (a previous round; superseded)

The repaired item compiles with the unchanged target signature. The open-section argument
uses `overPushforwardOverAdj` and the adjoint-triple unit criterion, and no duplicate
extension helper remains. The two existing new modules and their statements are unchanged
and compile with the item.

## New nodes

`lem-weil-pbc-module-inverse-image-unit-comparison` is delivered by
`lean/Sheaf/CategoryTheory/ModuleInverseImageUnitComparison.lean`.
`lem-weil-pbc-proetale-module-specialization-unit` is delivered by
`lean/Sheaf/AlgebraicGeometry/ProEtaleModuleSpecializationUnit.lean`.
The proof-context change record is `coord/changes/localization-proof-context.md`.


## Second reading by H1

1. **Interface: pass.** Compared every delivered module with the read-only repository.
   The sole existing public declaration is
   `AlgebraicGeometry.Scheme.proEtale_ringed_localization_sequence`; its signature,
   including universes, hypotheses, adjunctions and conclusion, is byte-for-byte
   identical. Its docstring and public imports are unchanged. The two helper modules
   are new, and no other existing module is adapted. The context-only change record
   documents the new private proof contexts; no mathematical interface changes.
2. **Proof and trust: pass.** Compiled all three modules in import order with
   `lcompile.py --all`. Read the local exactness descent, finite localization cover,
   sheafification vanishing, adjoint-triple counit proof, model-site equivalences,
   scalar-action adjunction and unit comparisons. No forbidden declaration or hole
   occurs. A scratch import with `#print axioms` for all three public theorems reports
   exactly `propext`, `Classical.choice`, `Quot.sound`. The action witness is obtained
   from an already proved construction; all carriers and units are fixed, and no
   arbitrary object is chosen from an unproved existence theorem.
3. **New statements: pass.** No statement is split off with `sorry`. Both new helpers
   are fully proved, strictly smaller steps of localization. Checked empty schemes,
   zero ring/module coefficients, empty closed support, and full closed support:
   empty sheaf sections are zero, while full support gives the unit comparison;
   the localization family also permits zero basic opens. The generic helper uses
   the ring-unit presentation, so it does not assert the false arbitrary-ring-map
   version of underlying pullback compatibility. Independent LeanFinder and Loogle
   queries found the existing Mathlib adjoint-triple criterion actually used here;
   scheme-open restriction counits found by LeanFinder have different sites and
   functors. Local searches found no existing proved specialization/module-unit
   comparison. The related G4 theorem `proEtaleModuleInverseImage_unitComparison_isIso`
   is still `sorry`; using it would add a reachable hole rather than shorten this
   complete proof.
4. **Route and pruning: pass after metadata repairs.** Checked the unit record
   `dag/units/sk-thm-properbasechange.json` and its three realized steps; this local
   geometric proof preserves them. The proof follows
   [Stacks 09AH](https://stacks.math.columbia.edu/tag/09AH), with the closed-section
   input [09AC](https://stacks.math.columbia.edu/tag/09AC) and module adjunction
   [03D2](https://stacks.math.columbia.edu/tag/03D2)/
   [03D3](https://stacks.math.columbia.edu/tag/03D3).
   Existing extension helpers from the parent module are not duplicated. Checked
   public versus proof-only imports: Ring.Limits and Grp.FilteredColimits in the new
   generic module are needed by its exported ring-forgetful and abelian-sheafification
   instances; making them private fails elaboration, so their public status is correct.
   Completed `No longer needed` with every removed direct import and old proof edge;
   distinguished transitive specialization input from genuinely bypassed edges.
5. **DAG: pass after correction.** Checked both new nodes, their source/proof
   docstrings, required metadata and matching Lean declarations. Existing node
   statement and Lean signature are unchanged. Corrected the open-piece proof step
   to describe `overPushforwardOverAdj` and the adjoint-triple criterion rather than
   the removed extension-presheaf construction. Removed proof edges to the unused
   derived-site and module-category wrappers, while preserving statement dependencies.
   The recorded proof dependencies are exactly the union of the proof-step uses.

Changed in this reading: completed hole/pruning accounting; corrected the main
node's open-piece proof and unused wrapper edges; refreshed the context-only change
record to match the delivered proof; added this independent review. The Lean proof
itself needed no repair. The temporary import-visibility experiment was reverted.
