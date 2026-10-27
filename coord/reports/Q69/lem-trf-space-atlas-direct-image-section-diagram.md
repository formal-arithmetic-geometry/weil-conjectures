## Worker report

The new module `Sheaf.AlgebraicGeometry.SpaceAtlasDirectImageSectionDiagram` states
`AlgebraicGeometry.AlgebraicSpace.space_atlas_direct_image_section_diagram`.
Its only postponed theorem is that declaration. Its docstring records all six proof
steps with the existing geometric, chart-limit, tensor, and composition inputs.
The auxiliary definitions contain actual maps and module data, with no sorry data.
`AtlasSectionComparison` packages the specified comparisons and their normalization;
`AtlasNestedTensorFormula` spells out the normalization on nested local tensors.
These helpers belong to this node's diagram, rather than introducing another
independent mathematical notion. All are listed in `lean.declarations`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `X Y : AlgebraicSpace S` and `f : X ⟶ Y`
  are precisely the algebraic spaces and their arbitrary morphism over that base.
- The scheme is `U : Over S`, regarded as `schemeSpace U`. The given map is
  `p : schemeSpace U ⟶ X`, with `hp : IsChartwiseEtale p`. For a scheme source,
  the first conjunct of the recorded `chartwise_etale_permanence` identifies this
  hypothesis with `IsEtale p.hom.hom`. This is an equivalent site interface, not
  an additional restriction. There is no affine, covering or surjectivity binder.
- The scheme overlap is supplied as `R : Over S` with maps `p₁ p₂`. The condition
  `IsPullback p₁.hom p₂.hom p.hom p.hom` is the universal property of precisely
  `U ×_X U` in fppf sheaves. Thus it retains the overlap, not an arbitrary relation.
  Its projections are étale (`h₁`, `h₂`), and `hr` gives their composite to `X`.
  `w : p₂ ≫ p = p₁ ≫ p` fixes the common map, hence the common `b`.
- `F` ranges over the recorded category `X.Modules`. The theorem is formulated
  for functors and natural transformations before quantifying over `F`, so the
  same choices work naturally for every module and every module morphism.
- `F_U` is the ACTUAL `(moduleTensorPullback p).obj F`. `F_R` is the ACTUAL
  `(moduleTensorPullback p₁).obj ((moduleTensorPullback p).obj F)`.
  `c` identifies the other actual iterated pullback with this one. The displayed
  `CU.restriction` pure-tensor formula and the two `AtlasNestedTensorFormula`
  clauses fix multiplication of coefficients, pullback of the inner coefficient,
  and restriction of the original section. Setting the coefficients to one gives
  the specified tensor-unit normalization. No globally pure-tensor hypothesis is
  made: these formulas refer to the existing local chart-unit tensor sections.
- The extension is the existing `(smallEnlargedModuleEquivalence X).inverse.obj F`,
  always with its specified counit to the original scheme-chart module sections.
- For every `V : Y.EtaleSite`, `W` is `(enlargedBaseChange f).obj
  ((enlargedSchemeInclusion Y).obj V)`. `atlasSectionObject f p hp V` is `Z`,
  and `atlasSectionObject f (p₁ ≫ p) hr V` is `Q`, both viewed over `X` by the
  existing enlarged postcomposition. The fibre-product convention writes
  `X ×_Y V`, `U ×_Y V`, `R ×_Y V` rather than the symmetric order in the node;
  the maps retain the same two projections and hence the same objects canonically.
- The first identification is the component of the natural isomorphism `α`.
  Its target is the explicit composite of extension by
  `(smallEnlargedModuleEquivalence.{u, u} X).inverse`, module pushforward along
  `enlargedStructuralMap f`, and `smallEnlargedModuleRestriction Y`.
  This is the module of extension sections on `W`, with its `O_Y(V)` action.
  The other two are
  `CU.sections F V` and `CR.sections F V`, explicitly `≃ₗ[O_Y(V)]`.
- The canonical first arrow is `ι`, and the relation arrows are `r₁ r₂`. They are
  natural transformations between precisely the three specified direct-image
  functors. The final three equations identify their values with extension
  restrictions along `atlasSectionToBase` and the two `atlasSectionArrow` maps.
  These maps are constructed with `pullback.map`: on coordinates they keep `V`
  and apply `p`, `p₁`, or `p₂`, respectively. These equations and the retained
  projections determine the arrows as the stated restrictions. The signature
  does not additionally assert an equation with an adjunction-unit/composition
  composite. The docstring describes that composite as the proof route to these
  restriction formulas; the report previously overstated what the signature says.
- `α` and all three arrows are morphisms/isomorphisms of sheaves of modules, so
  are linear and natural in `V` and `F`. `CU` and `CR` additionally include the
  explicit `moduleMap` and `testMap` equations for their section identifications.
- Every chart projection is retained: the first conjunct records the formula for
  `α` for every `q : ModuleChart f V`; `CU.projection` and `CR.projection` record
  the other two, after their specified tensor-to-restriction identifications.
  `atlasSectionProjection` is genuine extension restriction followed by the
  extension counit, not a freely chosen projection or a restricted chart family.
- Scalar actions on `Z` and `Q` are the actual `atlasSectionScalar`: pullback of
  functions to `W` via `enlargedStructuralMap f`, followed by restriction along
  the actual map to `W`. `AtlasSectionComparison.coefficient` states on EVERY
  scheme chart that this is exactly `moduleChartScalar (g ≫ f) V q`, the ordinary
  pullback of regular functions along its scheme map to `V`. Scalars on `W` use
  that same already-recorded structural map. These types keep coefficient and
  section universe `u` on sites whose objects can lie in universe `u+1`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `EtaleSite`, `structureSheaf`, `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `EnlargedEtaleSite`, `enlargedSchemeInclusion`, `enlargedBaseChange`,
  `enlargedPostcompose`, `chartwiseEtaleMap`, `enlargedStructureRestriction`,
  `enlargedStructuralMap`. The node's recorded umbrella module
  `Sheaf.AlgebraicGeometry.SchemeEtaleCotangentRingMap` is publicly imported and
  retains this interface via `SpaceCotangentRingMap`, `AtlasEtaleRestriction`
  and `SmallEnlargedEtaleModules`. Its current source and record were reread;
  the added ordinary-scheme ring-map interface does not alter these space maps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etale_fibreProduct_isScheme` (proof inputs).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleChart`,
  `moduleChartScalar`, `moduleDirectImageModel`, `moduleDirectImage`,
  `moduleTensorPullback`, `moduleTensorSection` (including its actual unit).
- `Sheaf.AlgebraicGeometry.SmallEnlargedEtaleModules`:
  `smallEnlargedModuleEquivalence` with original module universe `u`.
- `Sheaf.AlgebraicGeometry.SpaceChartLimitEnlargedSections`:
  `space_chart_limit_enlarged_sections` is a proof input, imported through the
  tensor-realization module. Its theorem-owned helpers are inlined in the
  statement: the direct-image composite, counit after extension restriction,
  and `enlargedChartLift` with the chart triangle's actual map and equation.
- `Sheaf.AlgebraicGeometry.SpaceChartTensorRealization`:
  `space_chart_adjunction_tensor_realization` is a proof input (plain import).
  The statement inlines its restriction functor as Mathlib
  `SheafOfModules.pushforward (F := chartwiseEtaleMap g hg) ⟨𝟙 _⟩`, and each
  chart arrow as the explicitly typed `ObjectProperty.homMk q.hom`.
- `def-sfb-space-chartwise-etale-morphism` is now a statement dependency. Its
  existing declaration is `AlgebraicGeometry.AlgebraicSpace.IsChartwiseEtale`
  in `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`. Its exact definition
  and record were reread: every representable étale scheme chart composes to
  a representable étale map, without requiring the space map representable.
- `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`:
  `chartwise_etale_permanence` (including scheme-source equivalence).
- `Sheaf.AlgebraicGeometry.EnlargedRingedCompositionLocalization`:
  projection-normalized enlarged composition/localization (plain proof import).

Sources checked: the full statement and proof of Stacks Tag 03M8 in
`literature/stacks-project/spaces-morphisms.tex`, together with the recorded
interfaces and proof plans. The latest blueprint's ancestor
`lem-trf-local-term-locality` and unit `sk-i-curve-zero` were also read. This
historical helper is not their own statement; it extracts only the section
identifications from 03M8, which do not require the covering assumption used
later in that tag for exactness. No statement correction is needed.

Searches performed via the prescribed `msearch.py` wrapper:

- LeanFinder, query "Direct image module sections algebraic space etale atlas
  restriction diagram with chart projections": 8 hits, including
  `ModuleCat.Tilde.res_apply` and scheme restriction. No algebraic-space diagram.
- Loogle, query `SheafOfModules.pushforward, SheafOfModules.pullback`: 12 hits,
  abstract pullback/adjunction/composition API; no atlas section theorem.
- Mathlib grep, `atlas.*[Dd]irect|[Ee]nlarged.*[Ss]ection`, subdirectory
  `AlgebraicGeometry`: no hits.
- LeanSearch, query "Etale atlas direct image sections restriction diagram on
  the enlarged site of an algebraic space": 8 hits, including `Sheaf.ΓRes`
  and scheme étale topology/restrictions; no match.
- `rg` over both project Lean roots for the node ID, `atlasDirectImage`,
  `atlas_direct_image`, and the new declaration names: no existing match.
  Broader searches inspected the existing atlas equalizer, étale restriction,
  chart-limit, tensor realization and flat-base-change modules. The equalizer
  theorem assumes an affine, surjective atlas; the chart-limit theorem treats
  one morphism, not the three compatible tensor-pullback vertices and arrows.
  Thus neither is an exact existing declaration for this node. No notion is copied.

Edge cases checked before writing and again against the final signature:
empty `U` and empty overlap; empty base or target scheme; `p = id`; a proper
non-surjective open immersion; the zero module; arbitrary non-representable `f`;
non-affine `U`; both relation projections; coefficient universes smaller than
the all-chart category. There is no covering or nonemptiness hypothesis, no
exactness conclusion, and no imposed equality of site and module universes.
The two relation maps retain their distinct coordinate maps, even when they
coincide in an identity/open-immersion case. All variables and universes are
explicitly bound, and `autoImplicit` is disabled.

No statement dispute, dependency module, new independent definition node, or
change to the mathematical statement or accepted proof split. The returned
packet's `stmt_deps` gains the existing definition owner named above; its `lean`
record is regenerated from the inlined signature. No other node fields change.

## Second reading by Q69

A separate in-thread reading reopened the node and the final module and checked
the correspondence above against every hypothesis and clause. The dispatcher
explicitly prohibits starting other agents, so this is a self-review, not a claim
of an independent worker review; the maintainer's independent delivery review
remains the independent reading. No mathematical mismatch was found. In particular,
the reading checked the actual iterated tensor functor at the third vertex, both
nested-tensor normalizations (including the second path's comparison `c`), the
common `b` supplied by the pullback equation, every chart-projection field, both
naturality equations, and the chart-normalized coefficient field. The auxiliary
maps were checked to retain the test-scheme coordinate. A reversed commutative
square equality in their constructor was repaired during compiler validation;
this changes no mathematical statement. All theorem proofs remain `sorry`.

Original-head validation (before the present repair): the module compiled and
passed delivery preflight at returned head `5ad392d9e0db`. The repaired file is
recompiled and checked afresh below; the old result is not used as validation
of the changed file.


## Returned delivery repair

Return at immutable head `5ad392d9e0db`, H2:

1. Added `def-sfb-space-chartwise-etale-morphism` to the item's `stmt_deps`,
   using its already-landed `existing: true` record. Its module and signature
   were read in the current shared clone. The retained returned node differs
   from current main only in its undelivered `lean` record; main still has no
   Lean binding for this item. No dependency node is rewritten.
2. Inlined all five named theorem-owned helpers throughout the module:
   `enlargedSmallModuleDirectImage` becomes its exact three-functor composite;
   `enlargedModuleChartRestriction` becomes the extension counit applied after
   the actual restriction map; `enlargedModuleChartLift` becomes
   `enlargedChartLift` with the chart triangle; `chartTensorEtaleRestriction`
   becomes Mathlib pushforward along the chartwise-étale site functor with its
   identity structure-ring map; `chartTensorEtaleArrow` becomes the same typed
   `ObjectProperty.homMk` of the chart triangle. No renamed helper or duplicate
   definition is introduced. Searches confirm none of those five names remains
   anywhere in the repaired Lean module. The proof-only tensor-realization and
   permanence modules are plain imports; the actual module operations are a
   public statement import.
3. Corrected the advisory report error: the arrows are characterized by their
   restriction equations and the retained chart projections. The Lean signature
   does not assert an additional equality with the adjunction-unit/composition
   composite. The proof docstring describes the unit computation as its proof
   route, as in the unchanged six-step DAG proof. No mathematical strengthening
   or weakening has been made by this documentation correction.

Self-review reopened the changed module and node and compared the five expansions
with their original defining bodies. The substitutions are definitional, with the
same universes, functions, scalar maps and counit, so all previously reviewed
hypotheses and clauses are retained. `hp`, `h₁`, `h₂`, `hr` are unchanged; their
predicate now has its explicit DAG definition owner. The nested-tensor `c`, all
three restriction formulas, every projection, both naturality fields, and the
scalar-coefficient equation remain in place. The report's prior unit-equation
claim is removed. This addresses every requested H2 repair and the advisory.


Repair validation: the inlined file passed `scompile.py` under both the sandbox
name and final library module name, with no warning or error. On refreshing the
current dependency record afterward, its owning wrapper was found to be
`SchemeEtaleCotangentRingMap`, publicly retaining `SpaceCotangentRingMap`.
The single public import was updated to that recorded wrapper, with no change
to declarations or the theorem signature. The ensuing delivery dry run compiles
this final import list afresh against the current published server build.
