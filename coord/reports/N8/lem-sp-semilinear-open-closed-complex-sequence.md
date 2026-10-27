## Worker report

The module `Sheaf.Paper.SemilinearOpenClosedComplexSequence` states
`WeilConjectures.SemilinearSections.OpenClosed.semilinearOpenClosedComplexSequence`.
It uses the existing `SemilinearSections.Systems` category, not a new category of
systems or diagrams in derived categories. Its conclusion constructs `SequenceData`
and, for every compatible coefficient map, `ScalarCompatibility`. The helper
structures package the clauses of this node; no separate mathematical notion or
dependency definition is introduced. Definitions have actual data. The five
postponed theorems are named, listed in `lean.declarations`, and have source and
proof docstrings: continuity of sequence base change, naturality of its coefficient
unit, compatibility of localized and inverse-image coefficient maps, and the main
theorem. Every theorem proof is `sorry`.

Sources read: Stacks `proetale.tex`, labels
`lemma-ses-associated-to-open` (09AH) and
`lemma-closed-immersion-complement-retrocompact-exact` (09BM), and current blueprint
`sec-smooth-purity/sk-lem-sp-tower-bound/sk-lem-sp-tower-bound-operations.proof.md`,
paragraph (2), final sentence. The source assumes a quasi-compact complementary
open immersion; it does not assume that T is qcqs, nor boundedness of the complex.

Hypothesis and clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Scheme T and closed immersion i:Z→T | `{T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]` |
| Complementary quasi-compact open a | `(U : T.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]` and `_hU : Set.range U.hom = (Set.range i)ᶜ` |
| Small pro-etale sites | `Scheme.ProEt.topology`; objects have universe u+1 and morphisms universe u throughout |
| Arbitrary strict inverse sequence of ring sheaves | `B : ℕ → Sheaf (Scheme.ProEt.topology T) CommRingCat.{u+1}` and adjacent maps `τ`; `SemilinearSections.rings` composes these into the strict inverse sequence |
| Module systems and semilinear transitions | The existing `Systems` is `SheafOfModules` over `systemRing` on the vertical sequence topology; all horizontal restriction maps and their identity/composition laws are part of the presheaf data |
| Inverse-image ring towers | `inverseRings i B` and `inverseMaps i B τ` apply the recorded ring inverse image; the open presentation uses the actual `B n | U`, `openTower` and `openTowerMap` |
| Open module inverse image and extension by zero | `SequenceData.openPart : SequenceOpenOrdinary ...`, whose `L` is actual section restriction, and whose `Jfun` evaluates to `localizedSystemExtension`, the published direct-sum presheaf followed by module sheafification |
| Open identification with U's pro-etale site | The slice presentation is explicitly permitted by the node. The imported `sequenceSiteOpenExtension` uses `Scheme.ProEt.sliceEquiv` and its covering topology; `U.hom` is the immersion a |
| Closed ordinary direct image | `push` is `SheafOfModules.pushforward (moduleUnit i B τ)` on the actual sequence site; on (n,V) its sections are those on (n,V×T Z) |
| Closed ordinary inverse image | `pull` is `SheafOfModules.pullback` for exactly that ring unit; it is a uniquely determined left adjoint to the specified pushforward, not a choice of unrelated functor |
| Coefficient action and transitions | `coefficientUnit` has component `((proEtaleSheafAdjunction i CommRingCat).unit.app (B n)).hom.app V`; `unit_naturality` covers every product-site arrow, including every horizontal composite |
| Exactness of all four functors | Open exactness/additivity are fields of `SequenceOpenOrdinary`; closed exactness/additivity are `pullAdditive`, `pullLimits`, `pullColimits`, `pushAdditive`, `pushLimits`, `pushColimits` of `SequenceData` |
| Actual open counit and closed unit, naturally in systems | `openPart.adjunction.counit` and `(adjunction i B τ).unit`; these are natural transformations of actual system functors |
| Every unbounded cochain complex | `SequenceData.complexSequence : ∀ C : CochainComplex (Systems ...) ℤ, ...`, with no degree bound |
| Short exact sequence of complexes | The termwise open counit is `Mono`, the termwise closed unit is `Epi`, and their `ComposableArrows.mk₂` is `Exact`; together these are exactly categorical short exactness, including zero composite |
| Degreewise short exactness | In the abelian complex category, short exactness is equivalent to short exactness after every degree evaluation (`HomologicalComplex.shortExact_iff_degreewise_shortExact`) |
| Every coefficient-level evaluation has the canonical arrows | `openPart.level`, `restrictionLevel` and `counit_level` fix the open arrow; `pushEvaluation`, its identity-on-sections normalization, `pullEvaluation`, and `unitEvaluation` fix the closed arrow to `levelAdjunction.unit` |
| Same ordinary inverse image as the recorded dependency | `levelPresentation n : levelPull i (B n) ≅ proEtaleModuleInverseImage i (B n)` identifies the canonical original-site module pullback with the dependency's small-model presentation |
| Arrows commute with differentials | `Adjunction.mapHomologicalComplex (.up ℤ)` gives actual chain maps; their chain-map equations hold in the strict system category |
| All arrows and differentials commute with semilinear transitions, including composition | Every arrow is a morphism of module sheaves on the product site; product-site naturality includes all horizontal arrows and their compositions. `openTransitions` additionally gives the prescribed open extension/scalar-comparison transition formula |
| Every compatible B→D | The main theorem quantifies over every `D`, `σ`, `φ n : B n ⟶ D n`, and `hφ : φ (n+1) ≫ σ n = τ n ≫ φ n` |
| Actual scalar restriction | `scalar` abbreviates the existing `res (systemMap ... φ hφ)`; `openScalar` and `closedScalar` apply the actual localized and inverse-image coefficient maps |
| Scalar comparisons for all four operations | `ScalarCompatibility.openPull`, `openPush`, `closedPull`, `closedPush` |
| Comparisons preserve additive data | `openPull_sections` and `closedPush_sections` specify the section identities. Their adjoint comparisons are normalized by `openCounit` and `closedUnit`; these fix the adjoint maps, rather than allowing an arbitrary isomorphism |
| Actual sequence arrows, not just terms, commute with coefficient change | `openCounit` is the full counit equation after the open end-term comparison; `closedUnit` is the full closed-unit equation. Multiplying the latter by the inverse closed-pull comparison gives the claimed equation for the closed end term |
| Compatibility on complexes | The four comparisons are natural isomorphisms on systems. Applying them termwise gives natural isomorphisms on cochain complexes, and their displayed equations apply to every C.X q and its differential |
| No flatness, constructibility or normalization assumptions | None occurs in the binders. The normalization equations specify which canonical maps are asserted to exist, and impose no condition on the coefficients or input complexes |

Dependencies inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its quasi-compactness import:
  `QuasiCompact`; no finite-type assumption is imposed.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.SemilinearSystemModels`: `Systems`, `ring`, `ringPresheaf`,
  `systemRing`, `evaluation`, `res`, `systemMap`, and their section normalizations.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, used through `res`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` publicly reexports the
  arbitrary ring-sheaf operations. This statement uses their arbitrary ring-sheaf
  inverse image, base change, coefficient adjunction unit and module operations;
  it never specializes B to constant rings.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf`; and
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`. Both occur in the published open extension.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, the exact
  underlying module category used by `SemilinearSections.Mod`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Mathlib.Algebra.Homology.ExactSequence`: `ComposableArrows.Exact`.
- `Sheaf.Paper.SequenceSiteOpenExtension`: `SequenceOpenOrdinary`,
  `SequenceOpenOrdinary.Transitions`, `openTower`, `openTowerMap`;
  these are now cited through `def-pur-sequence-site-open-data`, without using
  the conclusion of the sequence-site existence theorem.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses`:
  `module_pushforward_isRightAdjoint_of_universes`. Its actual existing
  construction supplies the left adjoints at the separate site universes.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`, reexported by the recorded
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `proEtaleRingModules`, `proEtaleRingDirectImageMap` and
  `proEtaleRingModuleDirectImage`, with the identity identification of inverse
  coefficients. The ordinary ring sheaf is the `sheafCompose` expression used
  by `proEtaleRingModules`; no duplicate coefficient abbreviation is used.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` is a plain proof import:
  its open-closed theorem remains a proof dependency, and none of its duplicate
  coefficient/direct-image definitions occurs in the statement.
- The proof imports `Sheaf.Paper.RingedOpenScalarLimitCoherence`,
  `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`, and
  `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`, retaining the
  recorded proof route and scalar restriction input.

The added statement dependencies are the actual universe-general module
pullback existence instance, `lem-pur-ringed-site-module-pullback-exists-universes`,
and the definition-only attachment `def-pur-sequence-site-open-data`.
The two theorem nodes flagged by the independent return are not statement
dependencies. The original statement and all original proof dependencies are
retained; the original statement dependencies include
`def-weil-pbc-proetale-operations`, whose recorded definitions are now used.

Edge cases checked mathematically before writing: U empty and Z=T give the
identity closed-unit sequence; Z empty and U=T give the identity open-counit
sequence. The zero ring and zero complex remain permitted. Non-flat coefficient
maps such as Z/4→Z/2 only restrict actions, so no flatness hypothesis is needed.
Unbounded complexes and arbitrary degrees are covered by the integer complex
index. Non-qcqs T is allowed: the qcqs-only filtered-colimit clause of the
ringed localization theorem is not used. Equality indices and three-index
transitions are the identity/composition laws of the existing product presheaf.
Indexing by ℕ merely renames the displayed B₁,B₂,... to start at zero.

Searches actually run with `msearch.py` for this item:

- LeanFinder: “open closed short exact sequence of unbounded complexes of
  semilinear inverse systems of sheaves of modules”. Eight hits, including
  Mayer–Vietoris sheaf short exactness and degreewise complex exactness; none
  states this varying-ring pro-etale system result.
- Loogle: `SheafOfModules.restrictScalars, ShortComplex.ShortExact`. Zero hits;
  the response reports unknown identifier `ShortComplex.ShortExact` for this
  query. This unsuccessful name query was supplemented by LeanSearch.
- Mathlib grep: `semilinear|extensionByZero` in `CategoryTheory`. Zero hits.
- LeanSearch: “short exact sequence of complexes of semilinear systems of
  sheaves of modules”. Eight generic short-exactness/degreewise-exactness hits,
  including `HomologicalComplex.shortExact_of_degreewise_shortExact` and
  `ShortComplex.ShortExact`; no theorem with the specified ringed system maps.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` by the node id,
  semilinear/open-closed names and expected theorem names found no existing
  statement. It found the existing generic semilinear model, sequence-site open
  construction, ordinary ringed localization, and constant-coefficient proper/open
  APIs. The constant-coefficient proper/open API cannot express arbitrary Bₙ.

The sandbox and real library module both compiled cleanly through `scompile.py`
after making imported instance choices explicit and preserving distinct object
and morphism universes. No global build or direct source-repository mutation was
run. The saved packet was retained and repaired against the independent return at
immutable head `b687f19e7b34`; the initial dry run of the retained packet passed
mechanical checks (commit `c0b99f05cb0`), but did not resolve the returned ownership
issues. The module and node/report have therefore received substantive repairs.

No `STATEMENT-DISPUTED` issue or source-based statement correction was needed.

## Repair of independent return

(a) `levelUnit` now uses the exact `proEtaleRingDirectImageMap` of
`def-weil-pbc-proetale-operations`, with `S = inverseRings f R` at the given
level and `c = Iso.refl _`. Its source and target ring sheaves are the actual
`sheafCompose` expressions used in `proEtaleRingModules`. `levelAdjunction`,
`SequenceData.pushEvaluation` and `SequenceData.unitEvaluation` now explicitly
use `proEtaleRingModuleDirectImage f R (f⁻¹ R) (Iso.refl _)`.
`proEtaleModuleCoefficients` and `proEtaleRingedDirectImage` have no occurrence
in the revised module. The `lem-weil-pbc-proetale-ringed-open-closed` statement
dependency was removed; its plain proof import and original proof dependency
remain. The adjunction is still the real module pullback/pushforward adjunction,
so the unit equation fixes the identical canonical arrow.

(b) `def-pur-sequence-site-open-data` attaches the unchanged definitions
`openTower`, `openTowerMap`, `openExtensionSection`, `SequenceOpenCoefficientData`,
`SequenceOpenOrdinary` and `SequenceOpenOrdinary.Transitions` in the published
`Sheaf.Paper.SequenceSiteOpenExtension`. The item cites this definition node
instead of the theorem node `lem-pur-sequence-site-open-extension`. The existence
theorem is neither assumed nor used in the signature. This is precisely the
new existing:true definition node permitted in the return.

The genuine instance use of
`lem-pur-ringed-site-module-pullback-exists-universes` is retained unchanged,
as requested by the PASS on that point.

## New nodes

`def-pur-sequence-site-open-data` defines the existing ordinary open-extension
data on the ringed sequence site, including actual slice rings and maps,
normalized coefficient comparisons, the geometric localization, the two module
adjunctions, exactness data, level unit/counit equations and the transition
predicate. Its `existing: true` record names the six published definitions;
no module or definition is copied. The source is Stacks sites-modules.tex
03DI/03DJ/03CY and sites.tex 04GZ/0791, applied in blueprint operations.proof.md
paragraph (2). LeanSearch and LeanFinder queries for ordinary sequence-site
open extension returned generic function/module extensions only; Mathlib grep
of `SequenceOpenOrdinary|SequenceOpenCoefficientData|openTowerMap` found no hits.
Direct searches of `lean/WeilConjectures`, `lean/Sheaf` and `dag/nodes` found the
exact definitions only in the published module and its theorem-node attachment;
`blueprint_refs.py search SequenceOpenOrdinary` found zero blueprint nodes.
The literal tool results are recorded in the new node's `mathlib_searches`.
The new node's source statement defines a datum and a predicate, with no
existence theorem, derived assertion or extra mathematical assumption.

## Second reading by N8

Repair self-check by the same worker (no other agents were started, as the
repair brief requires). I opened the retained item, the revised module, the
published ordinary operation definitions, and every field of the unchanged
ordinary open datum and transition predicate. The original clause table still
matches all scheme, immersion, ring tower, complex and scalar-change binders.
The main theorem signature is byte-identical to the saved packet. In particular,
`complexSequence` still asserts Mono, Epi and Exact on the unbounded integer
complex; both comparison normalizations retain their actual sections, and the
closed unit equation now names the recorded identified-coefficient direct image.
The level pullback is the same canonical adjoint and `levelPresentation` retains
the original small-site presentation. The new definition record lists only
ordinary definitions, and its statement follows the source module field by
field; `Transitions` is a predicate, so no unused theorem conclusion is cited.
Neither repair changes the empty-open, empty-closed, zero-ring, nonflat scalar,
unbounded-degree or non-qcqs cases checked above. No statement correction or
new proof is introduced. `scompile.py` compiled the revised sandbox module
(8.5 s) and real module path (8.9 s) cleanly, with no unexpected warning.
