## What changed

Withdraw the assigned module and the 28 other unused modules listed in `deleted.txt`,
as the launcher explicitly directs. The delivery tool materializes each path as an empty
`module` file. Remove only the Lean attachment of their 35 existing DAG nodes
(`lean: null`); preserve every node statement, proof plan and source.

P3 landed the complete replacement route during this session (landing
`20261014T140636-L-118125`). The live proofs of
`AlgebraicGeometry.smooth_proper_diagonal_tensor_formula` and
`AlgebraicGeometry.exists_rightAdjointTensorComparison_projection` already use
shift-saturated perfect generation and the three proved helper modules. This delivery
uses that landed route and does not resubmit the obsolete E2 versions of those modules.

The source audit in `scratchpad/withdrawal-source-audit.json` confirms no outside
importer of any withdrawn module, no withdrawn module reached by `TargetsCheck` or
`Challenge`, and no withdrawn node realizing a unit statement or proof step. The assigned
module belongs to E2; the other 28 modules are unclaimed. No forced adaptation is needed.

Validation artifacts: `scratchpad/withdrawal-route-validation.log` checks the landed route,
its two unchanged direct consumers and all 15 public route declarations by `#print axioms`.
`scratchpad/withdrawal-empty-validation.log` checks the exact empty-module template
for all 29 withdrawals. Both use only the permitted lcompile command, one file at a time.
The global build remains the maintainer’s responsibility.

The required dry run printed `OK (dry run)` and passed the preflight except for
the second reading, which the second reader writes. Nothing was pushed.
Evidence: `scratchpad/withdrawal-dry-run.log`.

Change record: `coord/changes/retire-bounded-flat-normalization-branch.md`.

## Proved and sorry left

Proved 0 of the assigned module’s 1 direct sorry; split off 0. Retire
`AlgebraicGeometry.exists_bounded_flat_model_normalization`
(`lem-sc-bounded-flat-model-normalization`) by withdrawal. This is pruning, not a proof
or a decomposition of the normalization statement.

No sorry is left or added in the delivery. The 28 other withdrawn modules have no direct
sorry. No new theorem, definition or node is submitted. The landed replacement route
is independently compiled and checked; its proofs are credited to P3’s delivery.

## No longer needed

The following 29 modules are withdrawn together; their listed nodes lose only the
Lean attachment. All imports in these retired files disappear with the declarations.
The earlier 62-module pruning from the targets’ closure was already accomplished by P3;
this delivery removes the remaining 29 eligible source modules rather than claiming
another 62-module reduction of the targets’ closure.

- `Sheaf.Algebra.Homology.RelativeBiprodConeExtension`: `lem-sc-relative-biprod-cone-extension`.
- `Sheaf.Algebra.Homology.TensorShiftOneAssociator`: `lem-sc-total-tensor-shift-one-associator`.
- `Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization`: `def-sc-bounded-flat-shift-representative`, `lem-sc-bounded-flat-model-normalization`.
- `Sheaf.AlgebraicGeometry.CompactFlatBarUnionAugmentation`: `lem-sc-compact-flat-bar-union-augmentation`.
- `Sheaf.AlgebraicGeometry.CompactFlatGeneratorCover`: `lem-sc-compact-flat-generator-cover`.
- `Sheaf.AlgebraicGeometry.CompactFlatGeneratorRelativeExtension`: `lem-sc-compact-flat-generator-relative-extension`.
- `Sheaf.AlgebraicGeometry.CompactFlatGeneratorTowerResolution`: `lem-sc-compact-flat-generator-tower-resolution`.
- `Sheaf.AlgebraicGeometry.CompactFlatTelescopeBarEnlargement`: `lem-sc-compact-flat-telescope-bar-enlargement`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitAdjustmentFactor`: `lem-sc-derived-pullback-kflat-counit-shift-adjustment-factor`.
- `Sheaf.AlgebraicGeometry.FlatComparisonPreservesCountableCoproducts`: `lem-sc-flat-comparison-preserves-countable-coproducts`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeArrowBarData`: `lem-sc-flat-telescope-arrow-bar-data`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeArrowCocycles`: `lem-sc-flat-telescope-arrow-cocycles`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeArrowDiagram`: `lem-sc-flat-telescope-arrow-diagram`, `lem-sc-flat-telescope-arrow-diagram-construction`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationIsIso`: `lem-sc-flat-telescope-normalization-is-iso`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationUnshiftedIsIso`: `lem-sc-flat-telescope-normalization-unshifted-is-iso`.
- `Sheaf.AlgebraicGeometry.FlatTelescopePullbackSumColimit`: `lem-sc-flat-telescope-pullback-sum-colimit`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeStageMapRefinement`: `lem-sc-flat-telescope-stage-map-refinement`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeStageNaturality`: `lem-sc-flat-telescope-stage-naturality`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeSumComparisonIsIso`: `lem-sc-flat-telescope-sum-comparison-is-iso`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeSumModels`: `lem-sc-flat-telescope-sum-models`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeTargetRefinement`: `lem-sc-flat-telescope-target-refinement`.
- `Sheaf.AlgebraicGeometry.KFlatLocalizedConePresentation`: `lem-sc-kflat-localized-cone-presentation`.
- `Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitAssociativity`: `lem-sc-scheme-canonical-shift-unit-associativity`.
- `Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociator`: `lem-sc-scheme-canonical-tensor-shift-associator`.
- `Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociatorKFlatOne`: `lem-sc-scheme-canonical-tensor-shift-associator-kflat-one`.
- `Sheaf.AlgebraicGeometry.SchemeTensorShiftBinaryLocalizationSquare`: `lem-sc-scheme-tensor-shift-binary-localization-square`.
- `Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization`: `aux-sc-target-comparison-first`, `aux-sc-target-comparison-first-core`, `aux-sc-target-comparison-isIso`, `aux-sc-target-comparison-second`, `lem-sc-scheme-tensor-shift-localization-normalization`.
- `Sheaf.CategoryTheory.IntegerShiftFromOne`: `lem-sc-integer-shift-from-one`.
- `Sheaf.CategoryTheory.NatTransFromResolvingClass`: `lem-sc-nattrans-from-resolving-class`.

Five modules from the old branch are retained because they still have live side-route
clients: `CompactFlatFiniteSubcomplexDiagrams`, `DerivedPullbackKFlatCounitData`,
`DerivedPullbackShiftedUnitIsoData`, `FlatTelescopeStageMap`, and
`SchemeCanonicalShiftUnitIso`. Their sources and nodes are unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt retained the unused normalization sorry, so the delivery gate correctly
refused its packaging. The launcher’s withdrawal instruction resolves that gate without
proving, weakening or renaming the stronger normalization statement.

At session start seven legacy clients imported the assigned module. While checking their
imports, P3’s landed withdrawal removed three of them and the upstream normalization
chain. A fresh full-library reverse-import audit then identified the remaining closed
branch. Temporary predicate extraction and E2’s superseded helper modules were removed
from the submitted trees; they are retained only as scratchpad evidence.

The replacement argument uses invertibility at every shift, so its five-term triangle
argument can use independently transported components at A, B, A[1] and B[1]. It does
not require the unused supplied-tensorator normalization theorem. No claim that the
retired theorem is false is made. The unit and chapter routes are unchanged.

## Second reading by E2

Independent second reader, 2026-10-14. Verdict: pass as a declared withdrawal and
pruning delivery, not as a proof of bounded-flat normalization.

1. Compared all 29 complete old sources with the empty module that deliver3.py
   materializes; saved the literal diffs in scratchpad/second-reading-diffs.patch.
   Every old source in the change record matches the repository byte for byte.
   The removal of declarations is explicitly declared in that record. There are no
   retained declarations with changed signatures, no target changes, and no submitted
   replacement statements. The assigned module is held by E2; the other 28 are
   unclaimed. The current full source graph has no outside importer of any withdrawn
   module, so this set requires no adaptation of another group's work. Pass.
2. Compiled the exact empty-module replacements for all 29 files using lcompile.py,
   in scratchpad/second-reading-empty. Independently copied and compiled seven current
   route modules, including its two direct consumers, then compiled a scratch
   audit of the 15 public route declarations. Every axiom list contains only propext,
   Classical.choice and Quot.sound, with no sorryAx. The submitted empty modules
   introduce no theorem, data, arbitrary witness, sorry, axiom or unsafe declaration.
   Evidence: scratchpad/second-reading-empty-validation.log and
   scratchpad/second-reading-route-validation.log. Pass.
3. There are no split-off statements or new nodes to validate or search for. The old
   normalization theorem is withdrawn, not restated or claimed proved. Read the
   retained all-shifts predicate and its isomorphism, shift, retract, coproduct and
   cone proofs: empty coproducts and zero triangles use the same universal-property
   and exactness arguments, and arbitrary integer shifts use shiftFunctorAdd. Pass.
4. Read the two current application proofs and the three helper modules. They use
   the existing perfect case and perfect generation through invertibility at all
   shifts. The cone proof transports the independent components at A[1] and B[1]
   through exact functor shifts, so it needs no supplied-tensorator normalization.
   The report lists all 29 retired modules and all 35 detached nodes. Neither
   TargetsCheck nor Challenge reaches a withdrawn module. Checked every unit's
   realized fields: none names a withdrawn node; sk-thm-picard-duality and its route
   stay unchanged. All imports in an empty module disappear, and no new imports are
   delivered. This delivery claims no additional target-closure reduction after P3.
   Pass.
5. Compared all 35 node records with the repository: each changes only lean to null
   in the sandbox, which deliver3.py materializes by removing the attachment. The
   statements, proof, proof_deps, proof_origin and other fields are unchanged, and
   every repository node attached to a withdrawn module is included. The nodes keep
   their mathematical plans without falsely recording a Lean proof. Evidence:
   scratchpad/second-reading-source-audit.json and second-reading-holders.json. Pass.

Second reading changed only this report and added independent scratch validation
artifacts; the proposed Lean withdrawals and node edits needed no repair. Holes
proved: none (0 of 1). Holes added: none. The one retired hole is
AlgebraicGeometry.exists_bounded_flat_model_normalization, outside the current target
import closure; the target-closure hole net for this delivery is zero. The proved
replacement route belongs to P3's earlier landing.
