## Worker report

This delivery states `AlgebraicGeometry.ProEtaleWeilSheaf.native_proper_projection_realization`
in `Sheaf.Paper.NativeProperProjectionRealization`. Its proof is `sorry`. The concrete
helper definitions and `ProperSectionTensor` are in
`Sheaf.Paper.NativeProperProjectionComparisons`; definitions have real bodies; the conclusion packages the normalized comparison maps as data, without assuming
any projection isomorphism. The mathematical statement of the item is unchanged.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Finite field k₀ | `(k₀ : Type u) [Field k₀] [Finite k₀]` |
| Fixed algebraic closure and geometric base change | The recorded framework uses `AlgebraicClosure k₀`, `(X ↘ Spec (.of k₀)).geometricFiber` and `Scheme.Hom.geometricFiberMap p (comp_over p _)`. `NativeBaseChange.geometricMap` is the existing abbreviation of that actual map, reused directly from `Sheaf.WeilSheaf.GeometricProperBaseChange`. `properGeometricOver` and `properGeometricMapIsOver` supply its actual structure maps; the finite-type and quasi-compact instances reuse the existing base-change instances. No different Frobenius action or fixed-pair derived replacement is introduced. |
| Prime ℓ different from characteristic | `(l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]` |
| Ω with its native continuous coefficient sheaf | Existing `PadicAlgCl l`, `ProEtale.AdicSheaf`, and `LocallyFiniteAdicRealization.ringSheaf`; the latter is the section ring of the actual native coefficient object. `source` and `target` are normalized realizations for these exact rings. |
| Separated finite-type source and target | For each structure map, `[IsSeparated …] [LocallyOfFiniteType …] [QuasiCompact …]`. These are the usual separated finite-type hypotheses, including quasi-compactness. |
| Proper p₀, over k₀ | `(p : Z ⟶ Y) [p.IsOver (Spec (.of k₀))] [IsProper p]`; Mathlib's `IsProper` is separated, universally closed and locally finite type; universally closed implies quasi-compact. |
| Ambient ordinary derived categories of abelian Weil sheaves | `DerivedCategory (ProEtaleWeilSheaf k₀ l X)` throughout; no fixed pairs in the ordinary module derived category. |
| A and T arbitrary bounded constructible derived inputs | The natural isomorphism has domain `WeilComplex k₀ l Z × WeilComplex k₀ l Y`. `projectionMate` and `projectionForget` quantify over every such pair; there is no lisse, degree-zero, perfection or extra Tor hypothesis. |
| Termwise forgetting U | `properSectionForget`, `properSectionCochain`, `properSectionDerived` and `properSectionFactors`. The derived functor is exactly `nativeForget ⋙ sectionDerived`, where section modules retain the actual coefficient action. |
| Symmetric monoidal common-stage realization ρ | `source`, `target`, `sourceAt`, `targetAt`, `sourcePresentation`, `targetPresentation`, `sourceFinite`, `targetFinite`, `sourceHom`, `targetHom`: these are the actual normalized realization interfaces, including finite-stage normalization and ambient Hom/evaluation. Their exactness and equivalence/essential-image assertions come from `Realization`. |
| Canonical locally finite-span / locally finite-extension coefficient identification | The section ring is the section ring of the same native coefficient object; `Proper.Comparison.operations.functions` fixes the geometric coefficient map to precomposition on every section. The coefficient-ring realization theorem is imported for the proof. There is no replacement ring or arbitrary coefficient map. |
| Balanced pullback/tensor μ | `balanced : NativeProjectionTensorComparison k₀ l p`, using the existing native comparison data. Its sheaf map forgets to the recorded balanced module map; every functor, model and summand insertion is fixed by `compatibility`, and `models` localizes the actual total comparison on K-flat pairs. |
| Actual derived counit εᵂ | `nativeProjectionProperMate` is the `homEquiv` of `derivedUpperStarLowerStarAdjunction` applied to `balanced.mu` followed by `nativeDerivedTensor.map (Prod.mkHom counit (𝟙 _))`. |
| Natural isomorphism αᵂ in D(WY) | `projection : properNativeProjectionSource … ≅ properNativeProjectionTarget …`, and `projectionMate` identifies its hom component with the preceding actual counit mate. Naturality and inverse naturality are part of a natural isomorphism. |
| Canonical tensor comparisons after forgetting | `sourceTensor` and `targetTensor : ProperSectionTensor …`. `cochain` is fixed on every actual balanced pure-tensor generator by `generators`; `representative` fixes the derived comparison on all native K-flat pairs. Thus these are not arbitrary tensor isomorphisms chosen to make the projection square commute. |
| Canonical direct-image comparison computed by forgetting K-injectives | `pushSheaf` is identity on actual section elements by `pushSections`. `injective` asserts that the underlying termwise complex is K-injective. `pushRepresentative` is the equality of the two canonical cochain-to-derived pushforward computation maps on every equivariant K-injective complex. |
| Actual native and ordinary counits agree | `counit` is an equality of actual derived arrows for every ambient A, using `pull`, `push`, and the recorded ordinary derived adjunction. |
| UY(αᵂ) is the ordinary projection morphism | `projectionForget` is the complete conjugation square with the tensor, pullback and pushforward comparisons. `properOrdinaryProjection` explicitly uses `comparison.operations.adjunction.homEquiv`, its actual counit, and `comparison.tensor.tensor`. |
| Proper-realization comparisons (aₚ,bₚ) | `comparison : Proper.Comparison …` is exactly the recorded normalized proper-adjunction realization, with its integral, tensor, unit, mate and counit equations. |
| Ordinary projection is ρ of the common-stage projection | `projectionRealization` is the actual equality for every common-stage pair K,L, with source comparison `targetAt.tensor.inv` followed by `b`, and target comparison `b` followed by `sourceAt.tensor.inv` and `a`. `properCommonProjection` uses the actual `geometricCommonStageAdjunction` and `canonicalCommonStagePullbackTensor`. |
| Normalization Rp! ≅ Rp* | `properCommonProjection` is the proper counit mate: the compactification is `(identity,p)`, so the open factor and its tensor comparison are the identities. This is the stated proper normalization, rather than an independently chosen isomorphic projection arrow. |

Dependencies read and used:

- `def-sf-native-weil-derived-framework`: `WeilConjectures.WeilSheaf.LowerShriek`, and its
  re-exported `ProEtaleWeilSheaf`, `WeilComplex`, `WeilComplex.objectProperty`, `upperStar`,
  `lowerStar`, `WeilComplex.upperStar`, `WeilComplex.derivedLowerStar`. The source and target
  are precisely the recorded full subcategories of the actual native derived category.
- `def-sf-derived-weil-category-and-operations`: its tensor component is owned by
  `def-sf-native-derived-tensor-layer`, whose recorded module
  `Sheaf.Paper.DerivedWeilTensorOperations` is imported directly. It supplies
  `AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensor`, `NativeIsKFlat`,
  `nativeTensorTotal`, `nativeDerivedClosedComparison` and its K-flat models. Its Verdier
  declarations are not substituted for tensor.
- `lem-sf-adic-qbar-constructible-realization`:
  `Sheaf.Paper.AdicQbarConstructibleRealization`, declaration
  `WeilConjectures.AdicQbarRealization.adic_qbar_constructible_realization`, with
  `Realization`, `At`, `FiniteNormalization`, `HomLaws`, `sectionFunctor`, `sectionDerived`
  and `ordinary` from its public definition modules.
- `lem-sf-weil-native-closed-forgetful`: `Sheaf.Paper.NativeWeilClosedForgetful`,
  `AlgebraicGeometry.ProEtaleWeilSheaf.native_closed_forgetful`; its exact conservative
  termwise forgetful functor and normalized tensor models are used.
- `lem-sf-derived-weil-pullback-pushforward-adjunction`:
  `WeilConjectures.WeilSheaf.Localization`,
  `WeilComplex.upperStarDerivedLowerStarAdjunction` and the ambient adjunction it restricts,
  `ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction`. The ambient counit is used because
  the node explicitly asks for the arrow in D(W), with constructible inputs.
- `lem-sf-adic-proper-adjunction-realization`:
  `Sheaf.Paper.AdicProperAdjunctionRealization`,
  `WeilConjectures.AdicQbarRealization.Proper.Comparison` and
  `adic_proper_adjunction_realization`. In particular, the ordinary operations are the exact
  recorded coefficient-precomposition inverse/direct images; a and b retain the actual
  ordinary common-stage adjunction normalization.
- `def-sf-native-projection-tensor-comparison-data` owns
  `NativeProjectionTensorComparison`, its generic representative presentation and
  `nativeProjectionProperMate` in their original module
  `Sheaf.Paper.NativeCompactProjectionFormula`, via an `existing: true` record.
  That module now contains definitions only: its downstream theorem is separated into
  `Sheaf.Paper.NativeCompactProjectionFormulaTheorem`. Both proper-projection modules
  reuse the existing definitions and import no compact-projection theorem module.
- `AlgebraicGeometry.NativeBaseChange.geometricMap` from
  `Sheaf.WeilSheaf.GeometricProperBaseChange` is reused directly for the actual geometric
  fiber map; its full signature and source docstring were read during this repair. The
  geometric proper-base-change theorem is not used as an assumption or invoked.

All stated proof dependencies with a module are imported, using plain imports when used
only by the future proof. The Mathlib leaves for base-change stability and K-injective Hom
are available through the corresponding morphism modules and `DerivedCategory.KInjective`.

Edge cases checked before drafting: p=identity gives its ordinary identity-open counit
mate; zero A or T gives the unique zero-object arrow, still invertible between zero
objects; empty schemes impose no nonempty-site or positive-rank condition; tensor total
uses arbitrary integer bidegrees and the existing signed differential, with an unsigned
balanced comparison. The input T may have several nonzero cohomology degrees and requires
no extra finite-Tor assumption. Site objects retain universe u+1 and site morphisms u;
ordinary section modules and native categories both use their recorded universes.

Searches before writing:

- `msearch.py … leanfinder "proper projection formula for derived Weil sheaves compatible
  with forgetting Frobenius and continuous coefficient realization"`: 8 unrelated hits
  (profinite functions, module presentations and affine limits); no exact statement.
- `msearch.py … loogle "CategoryTheory.Adjunction, CategoryTheory.IsIso"`: generic adjunction
  and fully-faithfulness results, no native projection statement.
- `msearch.py … grep "projectionFormula|projection_formula|projectionMap" CategoryTheory`:
  0 hits.
- `msearch.py … leansearch "balanced pullback tensor comparison on K-flat complexes in
  derived categories of Weil sheaves"`: 8 generic pullback and flat-module hits, no native
  representative comparison. The separate leanfinder and grep queries for that data are
  recorded verbatim in the new definition node.
- `rg` of `lean/WeilConjectures/WeilSheaf` found the lisse projection formulas, which impose
  a lisse sheaf input and do not state this arbitrary-derived-input theorem. A search for
  the item's blueprint id in `lean/WeilConjectures` found no declaration.
- `rg` of `lean/Sheaf` found the existing balanced comparison and counit-mate definitions in
  `NativeCompactProjectionFormula`; the definitions are reused in that original module,
  while its downstream compact-projection theorem is separated into its own module. No native proper-realization theorem
  was found. The server source was also read with `scompile.py --source` for that module.
- `rg -l` on DAG nodes and `tools/blueprint_refs.py search 'proper projection'` found no
  independent definition node for the comparison package (the existing matches are the
  downstream compact-projection statement and its consumer).

No statement correction and no STATEMENT-DISPUTED flag are needed.

## New nodes

`def-sf-native-projection-tensor-comparison-data` records `existing: true` on
`Sheaf.Paper.NativeCompactProjectionFormula`, with no new declaration module. It uniquely
owns the existing `ProjectionTensorSummandNormalization`, `ProjectionTensorPresentation`,
`NativeProjectionTensorComparison`, and `nativeProjectionProperMate`. These definitions
remain verbatim in their original published source module. The generic presentation fixes
every actual sheaf map, total summand and K-flat localization; the mate uses the actual
adjunction counit. Its dependencies remain the framework, native operations and open
tensor presentation definitions. The original searches are preserved in its node: Mathlib
and upstream have no equivalent native data, while the project has precisely these four
existing definitions. The previously delivered `NativeProjectionTensorComparisonData`
module has been removed completely from the sandbox delivery.

`def-sf-native-proper-projection-comparison-data` still owns
`Sheaf.Paper.NativeProperProjectionComparisons`: exact section forgetting and its cochain
localization factor, the left-first section tensor comparison pinned on pure generators
and K-flat models, scoped geometric-fiber instances, and the actual ordinary/common-stage
proper counit-mate arrows. These definitions assert no projection invertibility. The
source is latest blueprint Step 1, BS 6.8.14--6.8.15 and Stacks 03EK, 012Z, 06YU and 08BJ.
LeanSearch returned eight generic sheaf-forgetful facts; Loogle and Mathlib grep found no
match. The project and DAG searches were also read. The existing
`NativeSectionClosed.TransportNormalized` uses a reversed-curried total and its Koszul
sign correction; this module uses the native left-first total and its actual insertions,
without exchanging tensor factors. `NativeDualRealization.Datum` and the geometric-section
comparison likewise do not define these fixed-realization projection constructions.

The geometric map remains the existing `NativeBaseChange.geometricMap`, reused directly.
The four geometric-fiber structure instances remain public reducible abbreviations with
`attribute [scoped instance]`; the result module explicitly opens their scope.

## Dependency modules

The earlier return explicitly permitted moving the compact-projection theorem to its own
module to prevent the future proof import cycle. This repair takes that alternative.

`Sheaf.Paper.NativeCompactProjectionFormula` retains all twelve of its original definitions
in their original module, with unchanged signatures, bodies and declaration docstrings.
Only the `native_compact_projection_formula` theorem block is removed. The unchanged
block, including its complete natural-language proof and `sorry`, is placed in
`Sheaf.Paper.NativeCompactProjectionFormulaTheorem`, which publicly imports the original
module. Its variables and universes are bound explicitly. The copied theorem node
`lem-sf-derived-weil-compact-projection-formula` changes only `lean`: the new theorem module
and file are recorded, and its declaration list contains its eight original compact
helpers (publicly re-exported from the old module) and its theorem. The four comparison
definitions belong only to the new definition node. Its signature is recorded verbatim;
no mathematical statement, proof dependency or source field changes.

The consumer `Sheaf.Paper.WeilCompactStructureTensorComparison` actually invokes the moved
theorem, so its public import is changed to the new theorem module. Its remaining source,
including its published proof, is unchanged. The other direct consumer,
`NativeWeilDualizingHomTransposition`, uses only `nativeConstructibleTensor`, which remains
in its original module, and needs no edit. All delivered consumer modules are compiled.

## Returned delivery repair

Returned immutable head: `95e62c1f9e07`. The return reports
`native_compact_projection_formula` in both its old and new modules. The delivered
original module removes that theorem completely; its sole delivered declaration is in
`NativeCompactProjectionFormulaTheorem`. The theorem block, including its docstring,
signature and `sorry`, matches the current server source verbatim. The original module
otherwise differs only by blank lines, and the direct consumer differs only by its
public import. A fresh comparison of all four sandbox node records with current server
records found only the authorized `lean` and item `stmt_deps` differences; both definition
nodes remain new.

The four balanced comparison definitions remain in their original module and are reused
through the new `existing: true` definition node. The compact theorem node owns its eight
original compact helpers and its theorem, while the new definition node owns exactly
the four balanced comparison/mate names. No declaration is renamed or duplicated. Both
proper-projection modules import the definitions module and have no import path to the
compact theorem module. Thus the explicitly permitted theorem split removes the future
stage-3 import cycle.

The return arose from a landing-tool index that unioned deleted base locations with new
locations. Earlier retries documented this failure without modifying or bypassing the
tool. The live maintainer tool now supplies `overlay_index`, which removes all origins
belonging to touched modules, inserts their delivered origins, and updates their imports.
Both preparation and final transaction checks use this complete replacement overlay.
This resolves the false duplicate rejection; the source split itself remains intact.

This retry also removes a concrete transitive import path missed in the earlier check:
`NativeProperProjectionComparisons` / `NativeProperProjectionRealization` imported
`DerivedWeilOperations`, then `VerdierDual`, then the compact-tensor consumer, then the
moved compact theorem. Both direct imports now name `DerivedWeilTensorOperations`, the
existing owning module of exactly the tensor declarations used here. The dependency
`def-sf-derived-weil-category-and-operations` already cites the tensor-layer definition
node, so these are the same recorded constructions, with no replacement definitions.
A recursive check of the effective source imports after this change found no path from
either proper-projection module to the downstream theorem module. The check was repeated
read-only against current server sources with all five delivered sources overlaid and
also found no path (17,348 and 17,349 imports visited respectively).

The earlier H4 repair reuses `NativeBaseChange.geometricMap` directly. The geometric-fiber
instances remain scoped. All mathematical hypotheses, arbitrary bounded constructible
inputs, actual counit mate, tensor/forget/realization squares, identity-open normalization
and checked edge cases are unchanged. No statement correction is required.

## Second reading by NC

The delivered section was the dispatched worker's own self-check, and it said so. That is not a
second reading (H11). This section replaces it with the maintainer review's clause-by-clause reading
of head 7b45b9d34d34 (an NC re-delivery whose Lean files are byte-identical to NA head
770fa80806ae). The reading compares the head with the node, with its source place
(blueprint fix-lem-tensor-adjunction.proof.md Step 1, second Hom bijection; BS 6.8.14 and 6.8.15)
and with the dependency declarations.

Node clause → Lean → verdict:

- **Finite k₀, ℓ ≠ char k₀, Ω = Q̄_ℓ** → `(k₀ : Type u) [Field k₀] [Finite k₀]`, `[Fact l.Prime]`,
  `[Fact (ringChar k₀ ≠ l)]`, `PadicAlgCl l`. Exact.
- **Z₀, Y₀ separated of finite type over k₀** → `IsSeparated`/`LocallyOfFiniteType`/`QuasiCompact`
  on both structure maps, with p over k₀. Exact; these are the framework's hypotheses.
- **p₀ proper, with geometric base change p** → `[IsProper p]` on the theorem only. The geometric
  map is the existing `NativeBaseChange.geometricMap k₀ p`. Exact, and no stronger.
- **Ambient D(W_V) and the bounded constructible full subcategories** → `DerivedCategory
  (ProEtaleWeilSheaf k₀ l V)` and `WeilComplex k₀ l V`. Exact; no fixed pairs in an ordinary
  derived category.
- **α^W is the transpose of (ε^W_A ⊗ 1)μ and is a natural isomorphism** → `projection`, with
  `projectionMate` equal to `nativeProjectionProperMate`. That is the `homEquiv` of
  `derivedUpperStarLowerStarAdjunction` applied to `mu.hom ≫ tensor.map (counit ⊗ 𝟙)`. Exact: it
  is the actual transpose, not an arbitrary isomorphism.
- **μ is the balanced pullback/tensor comparison** → `balanced : NativeProjectionTensorComparison`.
  Its sheaf map, its summands and its K-flat localization are pinned.
- **U_Y(α^W) is the ordinary projection morphism under the canonical comparisons, with actual
  counits** → `projectionForget`, a complete square. Exact. Its pieces are pinned as follows:
  - `sourceTensor` and `targetTensor` are pinned by `generators` and `representative`.
  - `push` is pinned by `pushSections` and by `pushRepresentative` on equivariant K-injectives.
  - `pull`, `pullTensor` and `counit` complete the square.
  - The target is `properOrdinaryProjection`, the `homEquiv` of the recorded ordinary adjunction.
- **Under (a_p, b_p), the ordinary arrow is ρ_Y of the common-stage projection, with Rp_! ≅ Rp_***
  → `projectionRealization` for every common-stage K and L. It uses
  `comparison : Proper.Comparison` and `properCommonProjection`, the common-stage counit mate with
  identity open factor. Exact.
- **T is an arbitrary bounded constructible derived object** → every clause quantifies over all
  `A : WeilComplex Z` and `T : WeilComplex Y`. There is no lisse, degree-zero or Tor hypothesis.
  Exact.

Edge cases checked: p = id; A = 0 or T = 0; empty schemes; multi-degree T with the signed total
differential (the balanced comparison has no sign). Universes are as recorded, and no variable is
unbound.

Re-delivery checks against the returned head 95e62c1f9e07:
- **Lean changes.** The only Lean change is in the two proper-projection modules. Each replaces the
  public import `Sheaf.Paper.DerivedWeilOperations` by `Sheaf.Paper.DerivedWeilTensorOperations`.
  - The new module is the recorded module of `def-sf-native-derived-tensor-layer`, which is in the
    item's closure through `def-sf-derived-weil-category-and-operations`.
  - An import-closure walk over side-live with the head overlaid confirms the path
    `DerivedWeilOperations → VerdierDual → WeilCompactStructureTensorComparison →
    NativeCompactProjectionFormulaTheorem`.
  - After the change, neither proper-projection module nor NCPF reaches the theorem module,
    `WeilCompactStructureTensorComparison` or `DerivedWeilOperations`. There is no stage-3 cycle.
- **Unchanged files.** NCPF, `NativeCompactProjectionFormulaTheorem`,
  `WeilCompactStructureTensorComparison` and the compact node are byte-identical to 95e6. That
  review checked them: a verbatim theorem move under the same binders, and the four names
  declared once and owned once.

Re-delivery check against NA head 770fa80806ae: all five Lean modules, the compact node and the
report sections other than this one are identical; only the group fields and the item's
`lean.note` change. Both new definition nodes again lack the stmt_deps added by the 770f review,
which were lost with that head. The import-closure walk and the owner check were re-run against
current side-live (b252b5afe77) with this head overlaid and give the same results.

Record fixes made in this review (the same gaps as on 95e6, e234 and 770f, lost with those heads):
- **`def-sf-native-projection-tensor-comparison-data`.** Its declarations use `nativeOpenPull`,
  `nativeOpenSheafTensor`, `nativeOpenTensorModel` and `nativeOpenTensorInsertion`, owned by
  `def-sf-native-open-tensor-operations`. They also use `OpenTensorRestrictionNormalization`, owned
  by `def-sf-generic-open-tensor-presentation`. Neither owner was in the node's closure. Both are
  now added and cited.
- **`def-sf-native-proper-projection-comparison-data`.** It uses `nativeForget` (owner
  `def-sf-native-weil-closed-models`), the native open operations, and
  `canonicalCommonStagePullbackTensor` (owner `def-pur-completed-pullback-tensor-comparison`).
  All three are now added and cited. This also closes the item's own gap: its statement uses
  `nativeOpenPull` directly.
- **Acyclicity.** No added edge creates a cycle: no closure reaches the item, the compact theorem
  or the new nodes.

Advisories:
- The consumer node `lem-sf-derived-weil-compact-projection-formula` states its theorem with
  `NativeProjectionTensorComparison` but does not cite the new definition node.
- That node also still lists `nativeConstructibleTensor`, which `def-sf-native-constructible-tensor`
  owns.
- A stage-2 fix cannot edit that node's fields other than `lean`, so neither point is fixed here.
- `NativeBaseChange.geometricMap` is owned by a theorem node
  (`lem-sf-geometric-native-proper-base-change`), and other definition nodes also use it uncited.

## Validation

After narrowing both imports, the prescribed `scompile.py` compiled all five delivered
modules against the current published build and source overlay, with no errors or
warnings. Every compile completed within 60 seconds:

| Module | Sandbox | Library/private overlay |
| --- | --- | --- |
| `NativeCompactProjectionFormula` | 38.1 s | 38.6 s |
| `NativeCompactProjectionFormulaTheorem` | 11.3 s | 9.4 s |
| `NativeProperProjectionComparisons` | 23.9 s | 25.6 s |
| `NativeProperProjectionRealization` | 55.8 s | 52.8 s |
| `WeilCompactStructureTensorComparison` | 14.0 s | 13.9 s |

A lexical declaration check found exactly one source location for each of the four
existing balanced comparison/mate names and for the moved compact theorem. Ownership
across all delivered node records is disjoint. The two proper-projection modules have
no import path to the compact theorem module in either the local effective tree or the
current server tree with the delivery overlaid. The duplicate geometric-map definition
remains removed, and all variables and universes remain explicitly bound.

## Landing-tool correction

Read-only inspection of the live server confirmed the maintainer's fix in
`tools/nt_parallel2.py`: `overlay_index` replaces the old origins of every touched module
for declarations and statement texts, updates imports and per-module index entries, and
is used before duplicate checks in both preparation and final transaction validation.
Rejected transaction candidates are not adopted. The worker made no tool changes.

Fresh server-source reads confirm one compact theorem in the base original module,
zero in the delivered original module, and one in the delivered theorem module. The
current delivery therefore removes the old origin and introduces precisely one new
origin, as the repaired landing check now models. Earlier blocked retries did not
submit unchanged compiles or pushes. This resumed delivery additionally narrows the two
imports to the existing tensor module, as detailed above, and has been freshly compiled.

## Final dry run

`deliver2.py NC lem-sf-native-proper-projection-realization --no-push` returned:
`OK (dry run): the retained split passes preflight and compilation; nothing pushed`.
The five delivered modules and the probe of the four reused existing declarations
passed. Both existing-module edits were accepted as consumer repairs.
