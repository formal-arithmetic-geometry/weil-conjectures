## Worker report

Module: `Sheaf.CategoryTheory.FlatScalarTowerLimitSquare`.
Main declaration: `CategoryTheory.FlatScalarTowerLimit.flatScalarTowerLimitSquare`.
This delivery states the item with one `sorry`; no theorem is proved. The node's
statement, proof and proof dependencies are unchanged. The already landed definition node
`def-weil-pbc-flat-ringed-diagram-input` and the new existing-declaration definition node
`def-weil-pbc-derived-tower-models` are added because their data interfaces are used directly.
The theorem node `lem-weil-pbc-exact-adjoint-tower-models` is not added to stmt_deps.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The small sites presenting U,V are `D,H` and `C,K`, with `SmallCategory` instances
  in arbitrary universe `u`. `x : FlatRingedDiagramInput K H` supplies the geometric
  morphism, the two coefficient systems and their compatible transported ring maps.
  Its `R.morphism` and `S.morphism` are the recorded `RingedToposMorphism`; `sameInverse`,
  `sameDirect`, `sameAdjunction` identify the geometric morphism. The underlying
  adjunction has finite-limit-preserving inverse image. This is not restricted to
  morphisms induced by functors between sites.
- `x.RU`, `x.SU`, `x.RV`, `x.SV` are sheaves of commutative rings; `aU,aV` are their
  scalar maps. `flatU,flatV` are the recorded flatness condition, equivalent to
  exact tensor extension. `x.R.inverse.ringUnderlying` and its S analogue are the
  transported ring isomorphisms; `x.coherent` is precisely the commuting ring square.
  `FlatRingedModuleImage.transpose` normalizes the induced module adjunction, so its
  inverse and direct images are not arbitrary additive lifts.
- `modulesRU`, `modulesSU`, `modulesRV`, `modulesSV` are abbreviations for the exact
  recorded `ringedSiteModules`, itself Mathlib's `SheafOfModules`. The ring-forgetful
  functor changes no sections. `scalarU`, `scalarV` are actual Mathlib
  `SheafOfModules.restrictScalars`, not abstract exact functors.
- The eight `HasDerivedCategory.{w}` binders are localization-size choices, with
  unrestricted `w`. `DerivedCategory` localizes unbounded integer cochain complexes
  at quasi-isomorphisms. Strict towers are `ℕᵒᵖ ⥤ modules...`, and THEN localized;
  they are not towers in the triangulated category. Index `n` means positive level
  `n+1`, as in both recorded strict-limit declarations. No tower level is omitted.
- `FR,FS` and `TR,TS` use the existing
  `ExactAdjointTowerModels.DerivedModel`: the ambient and termwise derived direct
  images, their actual universal right-derived units, and computation on K-injectives.
  `LRU,LSU,LRV,LSV` are the same existing model applied to ordinary inverse limit.
  Each `on_injectives` field is the K-injective-resolution computation in the node.
  These are choices of the specified total-derived functors, not extra exactness
  assumptions. `limitAdditive` supplies the additive instance from Mathlib's
  limit-preservation criterion, without adding an additivity hypothesis.
- `rU,rV,rtU,rtV`, together with `qU,qV,qtU,qtV`, are the exact-localization
  identifications of actual restriction on modules and towers. The data retain the
  factors even when a different equivalent localization model is chosen.
- `χ` and `d` bundle their ordinary and derived natural isomorphisms in
  `ScalarComparison`. Its `normalized` field is exactly conjugation by the
  universal units at K-injectives, with both localization factors retained.
  `ordinaryχ` is the underlying-identity equation in
  `FlatRingedDiagramInput.OrdinaryComparisonsNormalized` for the one-object case;
  `ordinaryd` identifies each tower component with that same ordinary map. Thus no
  arbitrary natural isomorphism with the same endpoints can replace either map.
  These are exactly the comparison conditions of the recorded flat-diagram lemma.
- `κR,κS : PushforwardComparison ...` are the canonical direct-image/limit maps.
  `projections` fixes their ordinary map as `limit.post`. `normalized` is the
  common-composite unit equation in `ringedTowerPushforwardLimitComparison`,
  restricted to K-injectives; this uniquely fixes the specified derived comparison.
- The conclusion existentially supplies `lambdaU` and `lambdaV`, including ordinary
  and derived natural ISOMORPHISMS. Its first two conjuncts fix the ordinary maps as
  `limit.post T (scalarU x)` and its V analogue. Postcomposing with every limit
  projection gives the restricted original projection, hence these send a compatible
  family to that very family, independent of the chosen presentation of a limit.
  Their `ScalarComparison.normalized` fields say on every K-injective tower that
  restriction of the S-unit followed by lambda and the R-localization factor equals
  the module-localization factor followed by Q of the ordinary comparison and the
  R-unit. This is exactly the required conjugation normalization.
- The final `∀ Z` equation, in Lean left-to-right composition order, is
  `rV(κS) ≫ lambdaV ≫ LRV(d) = χ ≫ FR(lambdaU) ≫ κR`.
  Reversing composition notation gives exactly the displayed equation of the node.
  All arrows are natural isomorphisms of derived strict-tower functors, so the
  equation is natural for every derived morphism. There is no finite-reduction,
  completeness, boundedness or exactness-of-products assumption.

Dependency declarations read and used:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, including its sectionwise construction.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`.
- `Sheaf.CategoryTheory.FlatRingedDiagramRestrictionDefs`:
  `CategoryTheory.FlatRingedDiagramInput`, `FlatRingedModuleImage`,
  `FlatRingedDiagramInput.OrdinaryComparisonsNormalized`.
- `Sheaf.CategoryTheory.FlatRingedDiagramRestriction`:
  `FlatRingedDiagramInput.flatRingedDiagramRestriction`; its complete comparison
  structures and normalization equations in the public dependency modules were read.
- `Sheaf.CategoryTheory.DiagramSiteRealization`:
  `CategoryTheory.exists_diagramSite_realization` (proof dependency imported).
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`:
  `CategoryTheory.ringedTowerPushforwardLimitComparison`; its ordinary `limit.post`
  characterization and composite-unit equation are retained in `PushforwardComparison`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`;
  its K-injective total-derived computation is encoded by the four limit models.
- `Sheaf.CategoryTheory.ExactAdjointTowerModels`:
  `CategoryTheory.ExactAdjointTowerModels.DerivedModel` and `tower` are reused;
  no new definition of a derived model or tower-complex functor is made.
- The remaining recorded proof modules are imported: `RingedSiteModules`,
  `RingedSiteKInjectiveResolutionsOfUniverses`, `KInjectiveTotalDerived`,
  `KInjectiveExactSquareComparison`, `Sites.GeometricInverseImageExact`,
  `Mathlib.CategoryTheory.Abelian.FunctorCategory` (through public imports),
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
  (`Adjunction.preservesKInjectiveComplexes`), and
  `Mathlib.CategoryTheory.Adjunction.Limits` (`Adjunction.rightAdjoint_preservesLimits`).

The module docstring and theorem docstring give the source and the node's eight-step
proof, retaining the projection calculation and cancellation of universal units.
The helper structures bundle this item's own comparison data. The category and scalar
helpers are transparent abbreviations, with no postponed data or private notation.

Edge cases checked before writing: the zero module and zero tower; zero coefficient
rings (no nontriviality assumed); identity scalar maps and identity geometric morphism;
constant towers and nonconstant transitions; empty sites and degenerate topoi; arbitrary
unbounded degrees; both coefficient positions U and V; arbitrary positive tower levels
including the first. No exact-products property is used. The input sites and coefficient
universe remain the common chosen universe of the recorded small-site interface; `ℕ`
need not live in that universe because termwise functors use Mathlib's unrestricted
whiskering, rather than the dependency abbreviation that requires its index in `Type u`.
This repairs the initial elaboration issue without imposing `u = 0`.

Searches for an existing statement (2026-10-21):

- `msearch.py ... leanfinder "Flat restriction of scalars commutes with derived inverse
  limit of strict towers compatibly with the normalized direct image comparison"`:
  eight hits, including `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`,
  `Module.Flat.trans`, and `AdicCompletion.flat_of_isNoetherian`; none is this normalized
  square on sheaves or derived strict towers.
- `msearch.py ... loogle "CategoryTheory.Limits.limit.post,
  CategoryTheory.Functor.mapDerivedCategory"`: zero hits.
- `msearch.py ... grep
  "restrictScalars.*(limit|derived)|derived.*restrictScalars|rightDerived.*[Ll]imit"`:
  one unrelated hit `PointwiseRightDerived.hasColimit` in
  `Mathlib/CategoryTheory/Functor/Derived/PointwiseRightDerived.lean`.
- `rg` of the item id and `flat.scalar.*limit|scalar.*tower.*limit` in
  `lean/WeilConjectures` and `lean/Sheaf`: no existing statement. Broader scalar/limit
  searches found completed-coefficient and arithmetic-tower results with different
  objects/hypotheses. The DAG's
  `lem-cbc-flat-scalar-direct-image-limit-coherence` is unstated and assumes exact
  countable products; it does not supply this stronger arbitrary-site statement.
- Read the actual restriction, localization, geometric-morphism, flat-diagram,
  strict-limit and direct-image/limit source interfaces before writing.

No statement dispute, correction or dependency module was necessary. The returned
H2 ownership issue is repaired by the existing-declaration definition node below.
An initially misspelled proof import was corrected to the dependency's actual recorded
module; there is no missing module. A reserved binder spelling and two width warnings
were also repaired. The only postponed proof is `flatScalarTowerLimitSquare`.

## Second reading by NV

The worker reread the full node and final module against the correspondence above.
This is a self-check, not a claim of an independent second agent: the dispatch explicitly
forbids starting other agents and assigns independent review to the maintainer.
The check caught and removed four unnecessary additivity assumptions by supplying the
Mathlib-derived `limitAdditive` abbreviation. It also checked that `χ` and `d` retain
the ordinary identity normalization and that `κR,κS` retain their common-composite units;
the square is not a hypothesis. Both U and V scalar-limit comparisons are conclusions.

## New nodes

`def-weil-pbc-derived-tower-models` is an `existing: true` record on
`Sheaf.CategoryTheory.ExactAdjointTowerModels`, owning exactly
`CategoryTheory.ExactAdjointTowerModels.tower` and
`CategoryTheory.ExactAdjointTowerModels.DerivedModel`. The source module is unchanged.
The first is Mathlib whiskering followed by degreewise application to complexes.
The second has exactly the four fields `functor`, `unit`, `universal`, and
`on_injectives`, for arbitrary abelian categories and arbitrary complex functor H.
The node defines data without asserting existence; the consumer supplies this data
directly and never uses `.choose` or `exists_models`. Its universal factorization
clause is exactly Mathlib's `IsRightDerivedFunctor` (left Kan extension).
The edge cases are zero categories, zero/additive identity functors and zero complexes;
there is no nonzero, exact-product, boundedness, adjunction or small-site assumption.
The object, morphism and localization universes remain as in the existing declarations.

New-node searches (2026-10-21): `msearch.py leansearch` with query
"Total right derived functor model with a universal unit invertible on K injective
complexes and levelwise functor on strict tower complexes" returned eight hits for
Mathlib's total-derived, bounded-below right-derived and universal-unit APIs.
`msearch.py loogle` with query
`CategoryTheory.Functor.IsRightDerivedFunctor, CochainComplex.IsKInjective` returned
zero hits. `msearch.py grep` with query
`structure DerivedModel|abbrev tower|IsRightDerivedFunctor` returned 25 hits, including
Mathlib's `IsRightDerivedFunctor` class. These provide ingredients, not this bundle.
The separate `rg` of DAG nodes and the CategoryTheory source directories of both
WeilConjectures and Sheaf found the exact two helpers in the existing project module
and their ancillary listing under the existence theorem; no definition node owned
them. The blueprint ancestor command identifies
`lemma-weil-pbc-completed-exchange-coherence`; its second proof paragraph was reread.
The blueprint search for "derived tower model" returned 20 nodes about derived limits,
coefficient towers, completion and related operations; none is this definition bundle.

## Repair of returned H2

The returned immutable head was 5703f407c8c9. The initial saved-packet dry run passed
(preflight and compile, temporary commit eeeeeb3c5fe), but that mechanical pass does
not settle declaration ownership. I replaced the added theorem dependency
`lem-weil-pbc-exact-adjoint-tower-models` with
`def-weil-pbc-derived-tower-models`, which registers exactly `tower` and `DerivedModel`
as existing definitions. No theorem node or library module is modified or copied.
The main Lean file, the item's statement, proof, proof dependencies, and signature
remain unchanged. The already landed flat-input definition dependency remains.

Second reading of the repair: the new node matches the two source declarations
clause by clause, including the universal unit and its K-injective invertibility.
The main module uses those plain data interfaces in ScalarComparison,
PushforwardComparison, and the eight model parameters. It neither calls nor chooses
from the existence theorem. The original correspondence above, including normalized
χ, d, κ, λ and the square for every Z, still applies unchanged.
