## What changed

In `Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison`, proved
`RingTensorCohomology.exists_affineDerivedBaseChangeComparison` with its existing
signature and all three clauses: the unique comparison through the K-flat span,
its cohomology comparison identity, and its value on arbitrary K-flat models with
both augmentation equations fixing the model identifications.

Retained four fully proved private helpers: `augmentation_quasiIso`,
`resolution_kFlat`, `resolution_quasiIso_map`, and
`restrictedExtension_quasiIso_of_kFlat`. The restricted-extension argument uses
`ModuleCat.exists_baseTensorOrdinaryIso`; its pure-tensor formula proves the
commuting square needed to transport quasi-isomorphisms.

Repair of the maintainer's return: removed the duplicate private
`RingTensorCohomology.scalarExtension_quasiIso_of_kFlat` declaration entirely.
Its three uses now apply the existing
`CochainComplex.scalarExtension_quasiIso_of_kFlat` directly. Although private,
that theorem is accessible with proof-only
`import all Sheaf.Algebra.Homology.KFlatScalarExtensionDerivedIso`, as already
used by `KFlatScalarExtensionCounit`. Replaced the direct proof-only import of
`MixedTensorKFlatQuasiIso` with that import. The `BaseTensorOrdinaryIso` import
remains. Updated the node's second proof step and proof dependency to
`lem-sc-kflat-scalar-extension-derived-iso`. No duplicate theorem is retained.

All public imports, existing signatures, definitions and visibility are unchanged. Updated the existing node's
`proof`, `proof_deps` and `proof_origin` to describe the formalized route and clearly
identify the still-unproved localization plan. No new module, node, or change record.

Sources read: Stacks [Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
(lemma-single-complex-base-change-condition, affine proof),
[Tag 064L](https://stacks.math.columbia.edu/tag/064L)
(lemma-derived-tor-quasi-isomorphism-other-side),
[Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
(lemma-derived-base-change), and [Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
(lemma-compare-base-change), using the Stacks website because the local clone does
not include the literature bodies.
The same sources named in the existing node remain authoritative.

## Proved and sorry left

Closed one of the original two holes:
`RingTensorCohomology.exists_affineDerivedBaseChangeComparison`
(node `lem-pc-affine-derived-base-change-comparison-map`). This is a complete Lean
proof from existing library declarations, with no new sorry and no decomposition.

One original hole remains, unchanged:
`RingTensorCohomology.exists_affineDerivedBaseChangeLocalization`
(node `lem-pc-affine-derived-base-change-comparison-map`). Added zero holes.

The completed theorem uses the existing `RingTensorCohomology.spanLeft_isIso`
and ordinary tensor comparison infrastructure. The current repository proves
`spanLeft_isIso`; nevertheless the locally compiled comparison theorem still has
an inherited `sorryAx` dependency, as the independent axiom check confirms. This report counts removal of the
local proof hole, not final axiom closure of the target. The four retained private helpers
are proved completely. The module compiles cleanly through lcompile.py, including
the arbitrary universes u and w; no flatness, boundedness or Tor-independence
hypothesis was added. Inverses occur only for maps proved invertible, and the
ordinary tensor isomorphisms used are determined by their pure-tensor formulas.

## No longer needed

Removed proof-only imports:

- `Sheaf.Algebra.Homology.MixedTensorKFlatQuasiIso`: the repair imports and
  applies the existing scalar-extension theorem instead. Its node
  `lem-pc-mixed-tensor-kflat-quasi-iso` is no longer a direct dependency of this
  node, but remains a transitive dependency of the imported existing theorem.
  This removes a duplicate proof, not the underlying mathematical obligation.

- `Sheaf.Algebra.Homology.DerivedChangeOfRings`:
  node `lem-pur-derived-change-of-rings` is unnecessary for the completed
  comparison theorem; direct ordinary-module K-flat tensor invariance suffices.
- `Sheaf.Algebra.Homology.KFlat`:
  node `def-pc-kflat-complex` is the sheaf predicate; the completed proof uses
  `def-pc-module-kflat-complex`, already publicly available from RingTensorCohomology.
- `Sheaf.Algebra.Homology.KFlatResolution`:
  node `lem-pc-kflat-resolution` is unnecessary here; the fixed functorial module
  resolution already has the needed augmentation and K-flatness theorems.
- `Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology`:
  not used by the completed comparison proof. Its node
  `lem-pc-derived-tensor-localization-cohomology` remains part of the explicitly
  retained plan for the still-open localization declaration; no claim that this
  localization obligation is mathematically pruned.

No longer required by this node's completed comparison route:
`lem-pur-derived-change-of-rings`, `def-pc-kflat-complex`, and
`lem-pc-kflat-resolution` and their modules listed above. Localization of tensor products and exactness of
localization remain in the unproved localization plan. Pruning is relative to
this item's route, not a claim that other target branches do not use these nodes.
The unit record `sk-thm-picard-semicon` has empty realized statement/step lists;
no unit statement or realized step was bypassed or changed.

## Where the brief, the DAG or earlier work was wrong

The original first step calls for applying sheaf-level K-flat resolutions and
derived change of rings on a one-point site. The recorded Lean declarations take
SheafOfModules complexes, whereas this item takes ordinary ModuleCat complexes.
No one-point-site equivalence is needed: existing functorial module flat
resolutions and the mixed tensor theorem give the required invariance directly.

The remaining localization lemma cannot simply be applied to the second theorem:
`derivedTensor_localization_cohomology` compares
`ModuleCat.BaseDerivedTensorCohomologyModel` objects on the A-resolution and its
Aq-localization. This item's statement requires natural tensor-algebra lifts of
the fixed `source` and `target` functors. A next worker must connect their
counit-compatible derived models to these functors, transport the A-actions and
comparison, and then assemble the localization isomorphisms and square. Existing
`exists_baseDerivedTensorCohomologyAction` constructs objectwise actions and
counit-compatible comparisons; it does not directly supply those natural lifts.
No false statement was found, and the remaining declaration was not weakened or
replaced by an equivalent restatement.

The previous delivery and second reading incorrectly treated the existing
private scalar-extension theorem as unavailable. The maintainer correctly
returned this duplicate; `import all` supplies the existing theorem without
changing any public interface. The previous second-reading section has been
removed for a fresh independent reading of this repaired version.

Local verification uses only lcompile.py and deliver3.py. The second reader
runs the required dry run and delivers through deliver3.py; no library build is run.


## Second reading by Q3

1. **Interfaces: PASS.** Read the complete repository/sandbox diff and used
   `stage3_delivery.diff_module` to check existing declarations. Both theorem
   signatures are byte for byte unchanged; no definition or existing visibility
   changed. Public imports are unchanged, and all added proof dependencies use
   plain imports (including `import all` for the existing private theorem).
   There is one delivered module, one existing node, and no change record or
   forced adaptation.

2. **Proof and axioms: PASS.** Compiled the delivered module through lcompile.py
   without errors or warnings. Regenerated a scratch copy from this repaired
   module and printed axioms of both public theorems and all four private helpers.
   Each helper uses only propext, Classical.choice and Quot.sound. The public
   comparison theorem also has inherited sorryAx, and the unchanged localization
   theorem has sorryAx. No prohibited declaration or kernel bypass occurs, and
   the sole local sorry is the reported, named localization theorem. No data
   definition was added. The ordinary tensor isomorphisms used inside the helper
   are determined by their pure-tensor equations, which also prove the required
   commuting square; every inverse in the main proof is of a proved isomorphism.

3. **Split statements and duplicates: PASS.** No statement was split off and
   no hole was added. Read the existing scalar-extension theorem and ordinary
   tensor isomorphism, checked all three direct calls of the former, and searched
   lean/Sheaf and lean/WeilConjectures using scalar extension, resolution and
   augmentation terminology. Additional msearch grep and Loogle searches found
   no shorter matching theorem. The removed duplicate is absent. The new private
   helpers specialize existing resolution facts or prove the needed restricted
   extension invariance; they leave no obligations. Zero complexes, identity
   quasi-isomorphisms, identity ring maps and zero coefficient rings require no
   extra hypothesis, and the tensor-induction square is valid in each case.

4. **Route and pruning: PASS.** Read the main proof from invertibility of the
   left span through cancellation, homology naturality and the arbitrary-model
   clause. The two model isomorphisms are constructed by the exact augmentation
   formulas in the statement, and their compatibility follows from augmentation
   and comparison naturality. The three removed old proof dependencies are all
   listed under No longer needed. The localization dependency is retained in the
   node's remaining plan even though its unused Lean import is removed. The
   scalar-extension dependency still transitively needs mixed tensor invariance;
   no transitive pruning claim is made. Read sk-thm-picard-semicon and its source
   route: its realized statement and step lists are empty, and none is bypassed
   or changed. The remaining localization theorem needs action lifts and model
   transport beyond a short application of the existing localization lemma;
   it was left unchanged rather than replaced by another hole.

5. **DAG: PASS.** Compared the existing node with its sandbox version. Only
   proof, proof_deps and proof_origin changed. The proof-dependency list is the
   union of the recorded step uses, covers the existing scalar-extension and
   ordinary tensor comparison results, and preserves the dependencies of the
   still-open localization plan. The proved and unproved parts are explicitly
   distinguished. No new node requires validation.

**Changes made by this reading:** regenerated the stale scratch axiom check
(which still contained the removed duplicate); corrected the report's outdated
remarks on spanLeft_isIso and delivery authorization; added this independent
review. The repaired Lean proof and node were already correct and were retained.
Local holes closed: exists_affineDerivedBaseChangeComparison (one of two).
Local holes left: exists_affineDerivedBaseChangeLocalization (one).
Holes added: none; no decomposition.
