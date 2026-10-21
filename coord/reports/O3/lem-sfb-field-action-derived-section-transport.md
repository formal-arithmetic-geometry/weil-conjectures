## Worker report

The module `Sheaf.AlgebraicGeometry.FieldActionDerivedSectionTransport` states
`AlgebraicGeometry.ProEtale.FieldActionTransport.field_action_derived_section_transport`.
Its conclusion is the explicitly defined proposition `Assertion k ks`. It asserts
existence of the whole compatible system; its structures are specifications of
that system, not assumptions added to the theorem. The sole postponed theorem
has the node's sixteen-step natural-language proof in its docstring. All helper
definitions, including both projection arrows, have actual bodies.

Clause-by-clause reading:

* Field and separable closure: explicit `k ks : Type u`, `[Field k]`, `[Field ks]`,
  `[Algebra k ks]`, `[IsSepClosure k ks]`. The group is literally `ks ≃ₐ[k] ks`
  with the imported Krull topology; the schemes are `Spec (.of k)` and the
  dependency's `geometricScheme`/`geometricProjection`.
* Compatible universes: pro-etale and profinite objects have their existing
  universes; module objects are in `Type (u+2)` with morphisms in `Type (u+1)`.
  All localizations use the common `u+2` universe. `pulledModulesDerived` is the
  standard localization instance, not a different derived category. In particular
  the general derived adjunction is instantiated in this universe instead of
  using a specialized interface that hardcodes a smaller localization universe.
* Any commutative condensed ring: `Coefficients` is the dependency's `CommMon`
  of abelian sheaves. It has no topology, discreteness, nontriviality or flatness
  assumption. `Modules R.toMon Y` is the recorded internal module category over
  the actual `coefficientRing Y R.toMon`.
* The internal condensed Galois action: `CondensedBar.Equivariant` is the recorded
  `CondensedAction.ActionModule`, not discrete or finite-quotient representations.
  `Assertion` asserts its abelian structure and `ForgetData` asserts exactness and
  conservativity of the existing forgetful functor, both ordinary and derived.
* Exact additive field equivalence: `FieldData.geometric : GeometricData ...`
  supplies exactly the dependency's section and variable-action normalizations;
  `FieldData.equivalence` makes its functor an equivalence. Additivity is the
  geometric data's existing field; an equivalence preserves finite limits and
  colimits. `Assertion` also asserts that its termwise derived equivalence is
  t-exact for the standard derived t-structures.
* The formula on every test and its action: `e.geometric.sections`,
  `e.geometric.normalization` and `e.geometric.action` are the original dependency
  fields. They use its actual `test`, `fibreMap`, `twist` and geometric restriction,
  so the action comes from field automorphisms rather than an arbitrary action.
* Every ring map: `Assertion` quantifies all `R R'` and `φ : R ⟶ R'` simultaneously.
  `scalarMap`, `extend`, `derivedExtend` and `scalarDerivedAdjunction` use the
  actual pulled-back ring map, ordinary balanced extension, total left derivation
  and canonical exact-restriction comparison. `ScalarTransport` supplies ordinary
  and derived extension in the action categories, a total-left-derived counit and
  its universal property. `derivedCounit_normalization` fixes that counit as the
  adjoint of the original ordinary scalar unit, and both commute with shifts. Its `AdjunctionSquare.transpose` equations preserve
  every adjunction bijection, hence both units and counits. `field_sections` fixes
  field restriction on each original section; `fieldComparison` fixes its derived
  comparison by its total-derived unit. The underlying scalar squares use the
  actual condensed `Mod.extendScalars`/`Mod.comap` adjunctions.
* Every qcqs structure morphism: `Assertion` quantifies `X : Scheme` with
  `[CompactSpace X] [QuasiSeparatedSpace X]` and the named `a : X ⟶ Spec k`.
  It uses the existing `OrdinaryData` geometric section functor, whose total right
  derived functor is the dependency's K. No boundedness assumption is imposed.
* Canonical `D(E_R) Ra_* ≅ K_R`: `GeometricTransport.ordinary` and `sections`
  fix the underived comparison on all tests. `tests` and `test_fibres` fix the
  base-change test map on each geometric fibre. `derived` is a natural isomorphism
  of functors on the unbounded derived category, and `derived_unit` specifies its
  actual total-right-derived-unit normalization.
* Beta: `scalarProjection` is the scalar-adjunction transpose of
  `F.map (adjX.unit.app M) ≫ ρ.hom.app (S.obj M)`, verbatim the two arrows in the
  node. `CoefficientTransport.restriction` is the existing normalized coefficient
  comparison interface, with `sections` equal to the identity on original sections.
  `projection` equates the transported structure projection with exactly this beta.
  `arithmetic_counit` also fixes the former as the geometric counit-adjoint map.
* Forgetting: `GeometricTransport.forgotten` identifies the forgotten K with the
  exact geometric pullback followed by actual total point direct image.
  `forgotten_unit` fixes the comparison by the underived geometric restriction
  and derived units, rather than choosing an arbitrary isomorphism.
* Displayed forgotten projection: `PointAdjunctionData` retains the actual point
  module functors and fixes unit and counit on underlying abelian sheaves.
  `PointScalar.normalization` is the derived ordinary mapMod/comap exchange.
  `pointProjection` pulls back the source, applies that exchange, then scalar
  extension of the counit, and transposes under the point geometric adjunction.
  `CoefficientTransport.forgotten_projection` equates forgotten beta with precisely
  this arrow, followed by the canonical geometric-pullback scalar exchange.
* Naturality: object comparisons are natural isomorphisms of functors, so they
  include every input map. `restriction_square` supplies the coefficient-restriction
  square for all rings, maps and derived inputs. `forgotten_restriction` supplies
  the corresponding square after forgetting, with `pointRestriction` normalized
  by the actual point direct image and its underlying identity. `derived_shift`, `forgotten_shift`
  and `restriction_shift` state compatibility with canonical shifts.
* Finite norm coefficients: for every prime `l` and finite field extension
  `E/ℚ_[l]`, `Assertion` installs the existing `coefficientExtensionNormedField`.
  `normCoefficients` bundles the existing norm-continuous coefficient ring;
  `LisseTransport.equivalence` uses the already defined `NormContinuousLisse` and
  `NormContinuousRepresentations`. Its `sections` realizes the SAME field functor
  on inverse images as `C(P,W)` with `moduleTopology E W`; `add`, `scalar`, `action`,
  `restriction`, `maps` specify all continuous scalar functions, generalized Galois
  elements, profinite restrictions and equivariant linear morphisms pointwise.

Dependency declarations used (the source signatures and docstrings were read):

* `Sheaf.Paper.ProfiniteTestObjectFunctor`:
  `AlgebraicGeometry.ProEtale.profinite_test_object_functor`, `profiniteToProEtOf`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
* `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `isCommMonObj_condensedRingObj`.
* `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`.
* `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `sectionModule`,
  `forgetAction`; the public `CondensedBar` aliases from the descent dependency.
* `Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent`: `Coefficients`, `Modules`,
  `GeometricData`, `OrdinaryData`, `test`, `twist`, `fibreMap`, `geometricScheme`,
  `geometricProjection`, `geometricSections`, `pointModules`, `pointAdjunction`,
  `CoefficientComparison`, `restrictX`, `restrictCondensed` and derived instances.
* `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`,
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`:
  canonical total `rightDerivedFunctor`/`leftDerivedFunctor`, their unit/counit,
  general `derivedAdjunction`, `mapDerivedCategoryRightDerivedAdjunction`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: recorded derived
  module framework; no replacement tensor product is defined.
* `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`.
* `Sheaf.Topology.ContinuousMapCondensedRing`: all-continuous coefficient sheaf.
* `Sheaf.Paper.NormContinuousMonodromyData`: `normContinuousRing`,
  `NormContinuousLisse`, `NormContinuousRepresentations`. Its landed definition node
  `def-sfb-norm-continuous-monodromy-data` is added to stmt_deps to reuse this notion.
* `Sheaf.AlgebraicGeometry.ContinuousCoefficientBasic`:
  `coefficientExtensionNormedField`; Mathlib `moduleTopology`, standard t-structure.

Edge cases checked before writing: empty profinite test (all section equalities
remain quantified over the actual empty object); zero ring and zero modules;
nonflat coefficient maps (no flatness used anywhere); unbounded complexes in
both directions; rank zero (the existing representation category quantifies a
basis on `Fin n`, permitting `n=0`); trivial Galois group (no nontriviality or
positive rank binder); identity coefficient maps and identity structure morphism
(the same normalized adjunctions and comparisons are still required).

Searches for an existing full statement:

* msearch LeanFinder: “An exact equivalence between proetale modules over a field
  and condensed modules with Galois action compatible with derived sections and
  coefficient extension”: eight results, none the normalized field/derived/scalar
  statement (only general condensed/profinite-free interfaces).
* msearch Loogle: `Functor.mapDerivedCategory, ContinuousRep`: no result; this
  service reported unknown `Functor.mapDerivedCategory` for that query.
* msearch Mathlib grep: `field_action|fieldAction|CondensedAction`: no result.
* rg of `lean/WeilConjectures` and `lean/Sheaf` for field action, geometric sections,
  action categories, point/scalar adjunctions and continuous monodromy: reused the
  declarations listed above; no theorem with the whole normalized statement.
  Exact item-id grep of `lean/WeilConjectures` found no existing statement.

The cited local Bhatt–Scholze PDF (Example 4.1.10, Definition 6.8.3,
Proposition 6.8.4) and current blueprint direct-images paragraph (3) were read.
No correction of the item statement is proposed. The helper definitions package
canonical data in the four new definition nodes listed below; all existing
functors and categories are retained.
No STATEMENT-DISPUTED issue found.

Validation: scompile.py compiled all five modules independently in dependency
order, in both sandbox and library modes, with no errors or unexpected warnings.
Every file stayed below the prescribed 60-second limit. The largest verified
per-file time was 48.9 seconds. The prescribed delivery preflight follows.


## New nodes

`def-sfb-field-action-transport-data` defines `FieldData` and its auxiliary
normalized-adjunction, derived-unit, point-adjunction and forgetting specifications.
The auxiliary `OrdinaryScalarTransport` also packages the ordinary scalar squares
and their normalized restriction comparison. The field datum contains the existing
geometric field section functor with its section
and action equations and the assertion that it is an equivalence. All scalar and
point functors are the existing ones. Source: Bhatt–Scholze Example 4.1.10 and the
item's ordinary derived normalization. Exact-word searches of the DAG, Mathlib,
WeilConjectures and Sheaf found no FieldData/GeometricTransport/ScalarTransport;
blueprint search returned zero matching nodes. LeanFinder returned only general
condensed adjunctions and Loogle no exact bundled interface. The generic existing
`squareExchange` and `normalizedAdjunctionSquare_transpose` calculate mates, rather
than define this normalized field datum. Search outputs are in mathlib_searches.

`def-sfb-field-action-scalar-transport-data` defines `ScalarTransport`: ordinary and
derived scalar adjunctions, fixed restriction comparisons and total-derived-counit
normalization, with canonical shifts. Its dependencies are the preceding data and
the already recorded scalar/derived interfaces. It has the same source and search
record; no canonical scalar functor is copied. No inhabitance assertion is hidden
inside the definition.

`def-sfb-field-action-geometric-transport-data` defines `GeometricTransport`,
`LisseTransport` and their actual projection arrows. It
uses the first two nodes and the existing geometric-section, test and
norm-continuous-monodromy definitions. Source: the item normalization, blueprint
paragraph (3), Bhatt–Scholze Definition 6.8.3 and Proposition 6.8.4. The same searches
found no such bundled canonical geometric data; the realized lisse/representation
categories were found and reused. The four definition modules split the large
interface into independently compiled files within the prescribed time limit.

The auxiliary exactness parameters on the geometric interfaces are supplied in
`Assertion` by the existing exact coefficient pullbacks and the equivalence
property of `FieldData`. They add no assumption to the main theorem. Its only
inputs are the two fields, algebra and separable-closure structure. Exact
forgetting and the point-adjunction data occur existentially in its conclusion.


`def-sfb-field-action-coefficient-transport-data` carries the coefficient portion
of the geometric specification in its own module: normalized structure and point
restriction, the scalar/pullback mate squares, and both exact projection equalities.
It imports the geometric and scalar data and asserts no inhabitance. Its source
and recorded searches are the same normalized coefficient portion of the item.
This last division keeps coefficient elaboration independently within the file
limit and makes the projection equalities easy to review.


Preflight repair: the first dry run compiled all files but required LeanSearch
records in addition to LeanFinder/Loogle/grep for each new node. Four actual
LeanSearch queries were run, one for each interface; each returned eight hits.
The base query found discrete condensed modules and finite Galois categories;
the scalar query found ordinary ModuleCat scalar adjunctions and general shift
identities; the geometric query found field normality and normalization diagrams;
the coefficient query found pointed Galois and coalgebra adjunctions. None is the
normalized internal field-action data here. Exact outputs are now recorded in
each new node's mathlib_searches. No Lean statement changed in this repair.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
