## Worker report

Stage 2, Q14: statement of `lem-zl-finite-restriction-coefficient-descent` in
`Sheaf.Paper.FiniteRestrictionCoefficientDescent`, declaration
`WeilConjectures.FiniteRestrictionCoefficient.finiteRestrictionCoefficientDescent`.
The theorem has `sorry`; its docstring gives the complete eight-step mathematical proof.
All helper definitions have real data. There is no statement correction, no disputed
statement and no dependency replacement. The four new definition nodes below record
interfaces needed to express the several clauses without rebuilding existing categories.

### Hypotheses and objects

| Node phrase | Lean rendering |
| --- | --- |
| Finite-field datum p,a,q,k0,k | `(D : FiniteFieldDatum.{u})`; the recorded datum contains the finite field, its algebraic closure and characteristic |
| Prime ell different from p | `(l : ℕ) [Fact l.Prime]`, `(hl : l ≠ D.p)` |
| Finite E/Qell, valuation ring, uniformizer, positive quotients | Each `A : AlgebraicallyClosedCoefficients.Index l Ω` uses `Coefficient.{u} l Ω A`, its recorded Padic valuation ring/uniformizer and existing positive-index coefficient system; no replacement DVR or quotient ring |
| Algebraic closure containing coefficient fields | `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`; all finite intermediate fields are quantified, using the recorded small coefficient models. The closure universe v remains independent of scheme universe u |
| Separated finite-type k-schemes X,Y | `[X.Over (Spec (.of D.k))]`, `[Y.Over ...]`; `[LocallyOfFiniteType (X ↘ ...)]`, `[QuasiCompact (X ↘ ...)]`, `[IsSeparated (X ↘ ...)]`, and the three corresponding Y instances |
| Finite k-morphism f | `(f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsFinite f]` |
| Geometric point over the fixed algebraically closed k | `(y : Spec (.of D.k) ⟶ Y)` |
| Fibre S, v,h | `Limits.pullback f y`, `pullback.fst f y`, `pullback.snd f y`; the fixed base-change conventions are imported |
| All points and their unique lifts | `FiniteCounitTowers.Points f y = {x // x ≫ f = y}` and the existing `FiniteCounitTowers.lift f y x` |
| R_W and its completed module category | Existing `scalarReductionSource`, `sfIntegralConstructibleCategory`, and the completed coefficient sheaf used by those declarations |
| Strict derived reductions and exact restriction | `reduction` is the reduction of the recorded derived-system calculus. The coefficient-system category retains quotient-linear transition maps. The full-system reconstruction uses its recorded `coefficientSequenceLimit` |
| Tower direct image | `G.image.integral A` and `G.fibreImage.integral A` are the existing normalized strict direct-image models, not arbitrary functors satisfying only an objectwise existence assertion |
| Completed pullback | `PullbackDiagram.functor` is the full-subcategory lift of `integralDerivedPullback`; its construction takes no arbitrary functor argument |

### Conclusions and their normalization

1. `Finite (FiniteCounitTowers.Points f y)` is the finite fibre-point clause.
   `Endpoints.limit` identifies the target with the product of the point pullbacks.
   In this finite additive situation it is the finite biproduct. `Endpoints.empty`
   explicitly gives `IsZero` for an empty fibre.
2. The three ambient functors are constructed from reduction, the actual sequence-site
   geometric functors, total right derivation and the derived limit. `exchange` derives
   `FiniteCounitTowers.exchange`, the specified unit-square-counit mate. `restriction`
   derives `FiniteCounitTowers.restriction`, the tuple of actual pulled-back counits.
   `IntegralDiagram.exchange` and `.restriction` merely lift these very components
   to the full subcategory. Neither is an existentially chosen arrow.
3. `G : Geometry` supplies scalar comparisons for f and h and completed pullbacks
   along y,v,h,x,i_x. `G.Normalized` invokes the recorded integral and rational direct
   image laws and requires the pullback comparisons to equal `scalarPullbackCompleted`.
   Thus preservation is asserted on the integral constructible categories.
4. `TowerAgreement l Ω f` and the corresponding assertion for h identify ordinary
   completed direct image with every prescribed Roos presentation. For every n the
   isomorphism followed by `M.projection ≫ Pi.π _ n` is exactly direct image of
   `sfDerivedReductionUnit`, followed by `sfDerivedRestrictionComparison`.
5. `I : IntegralComparisons` supplies integral scalar comparisons at all vertices;
   `N.source` and `N.middle` identify these vertices with the geometric composites.
   `N.ScalarNormalized` spells out their conjugation by the normalized geometric
   comparisons and the scalar square for every point projection.
6. `I.Laws` contains the multiplication-unit identity, the exchange square, and the
   restriction square as equalities of actual morphisms. `I.Coherent` is the full
   triple-extension equation with the prescribed balanced tensor associators on
   source and target. It applies to all inclusions, including identities and ramified
   ones; no relation between distinct fields' uniformizer exponents is assumed.
7. `TensorRestrictionFormula` explicitly states on every sequence-site section that
   scalar extension of each actual point counit component sends the sheafified tensor
   section a tensor m to a tensor the image of m under that component. The component
   is the existing counit restriction along i_x, with its composition comparisons.
   The section operation is the recorded `integralComparisonSequenceTensorSection`.
   This is an integral whole-system formula, before deriving or rationalizing.
8. `R : RationalComparisons` contains actual stage-system morphisms for all vertices
   and `StageSystem.Morphism.Hom` records for both arrows. Its `objects`, `maps`,
   `exchange_components`, `restriction_components`, and `scalar_components` fix the
   literal localizations, including the formula a tensor g maps to a tensor F(g).
   `HEq` only accommodates object equalities between the specified localizations;
   it does not weaken the equality of the displayed maps. Geometric pullbacks have
   the same raw rational object, pure-tensor map and comparison normalization.
9. `SectionsCompatible` asserts naturality of the specified normalized
   `pointSectionsScalarExtensionIso` on every integral arrow. On the rational stages
   it asserts naturality of the prescribed `pointRationalFibreScalarIso`. In particular
   these equations apply to both finite restriction arrows. The already recorded
   point sections functor and its scalar comparison are used unchanged.
10. The common-stage functors are `(R.diagram q).functor`. The two descended arrows
    are explicitly `RationalComparisons.descendedExchange` and
    `.descendedRestriction`, defined using `StageSystem.Morphism.descNatTrans`.
    That construction maps a representative by the source comparison, the stage
    functor, and inverse target comparison. StageSystem quotient identities,
    compositions and its Hom compatibility supply independence of representative
    and of finite field of definition, and carry equations between these arrows.
11. `∀ W, FiniteData l Ω W` supplies one finite stage for any finite indexed objects,
    arrows, distinguished triangles and equality witnesses. The output includes
    object isomorphisms, commuting arrow squares, distinguished triangle
    representatives, and equality of both transported arrows at that same stage.
12. `DirectImageDescent` retains the exact stage rational direct-image functor and
    inverse orientation of its normalized scalar comparison, together with
    `TExactDescent` and `HeartExactDescent`. The same conditional assertions are
    retained for the three vertex functors. `TExactDescent` uses both standard
    halves, every integer degree and the recorded common-stage classes.
    `HeartExactDescent` supplies an additive heart functor with the literal included
    object and arrow formulas, preserving every `ShortComplex.ShortExact`.

### Dependency declarations used

All names below are read in their recorded modules; no private replacement is made.

| Module | Declarations used |
| --- | --- |
| `Sheaf.Paper.FiniteFieldFiber` | `FiniteFieldDatum` |
| `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and existing coefficient imports | `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer` |
| `Mathlib.AlgebraicGeometry.Morphisms.Finite` | `AlgebraicGeometry.IsFinite`; standard finite-type, quasi-compact, separated and Over classes |
| `Sheaf.Paper.SfIntegralConstructible` and `Sheaf.Paper.SfDerivedDirectImage` | `sfIntegralConstructibleCategory`, `sfIntegralConstructible`, `SfIntegralDirectImage`, `sfDirectImageTerm` |
| `Sheaf.Paper.IntegralDerivedOperationsOnSlices` / recorded intrinsic operation imports | `integralDerivedPullback`, `integralScalarExtension` |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | `coefficientDerivedSystemEvaluationCalculus`, its normalized reduction, `coefficientSequenceLimit` |
| `Sheaf.Paper.FiniteCounitRestrictionTowers` | `Points`, `lift`, `pull`, `push`, `pointSum`, `exchange`, `restriction`, `component` |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | `integralComparisonSequenceScalarModel`, `integralComparisonSequenceTensorSection` |
| `Sheaf.Paper.SfStrictDirectImageScalarComparison` | `IntegralComparisons`, `Comparisons`, `HasIntegralLaws`, `HasComparisonLaws`, `integralUnit` |
| `Sheaf.Paper.SfScalarExtensionComposition` | `sfIntegralScalarComp`, `sfIntegralScalarUnit`, rational scalar unit and composition |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | `scalarPullbackCompleted` |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | `AlgebraicallyClosedCoefficients.Index`, `Coefficient`, `coefficientInclusion`, `coefficientInclusion_laws`; `GeneralAlgebraicallyClosedCoefficients.Stage`, `stageSystem`, `integralTransition`, `transition`, `stageTransition`, `inclusion` |
| `Sheaf.Paper.SfConstructibleHeart` | `sfRationalStandardClass`, `sfCommonStageStandardClass`, `sfCommonStageHeart` |
| `Sheaf.Paper.FiniteCoefficientPoint` | `pointCompletedDerivedSections`, `pointIntegralModuleDerivedTensor`, `pointRationalFibre`, `pointIntegralConstructible_iff` |
| `Sheaf.Paper.PointSectionsScalarExtension` | `pointSectionsScalarExtensionIso`, `pointRationalFibreScalarIso` |
| `WeilConjectures.CategoryTheory.StageSystem.Functor` | `StageSystem.Morphism`, `.Hom`, `.functor`, `.descNatTrans` |
| `Sheaf.CategoryTheory.StageSystemFunctorDescent` | the representative-normalized coefficient pair functor interface, reusing the actual StageSystem carrier |
| `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses` | `SheafOfModules.isGrothendieckAbelianOfUniverses`, used to infer the existing K-injective instance on the sequence site |

The sequence K-injective instance is inferred from the recorded Grothendieck-abelian
structure; it contains no postponed proof. Other definitional proof fields are only
naturality inherited from the exact existing natural transformations. The theorem is
the only new postponed proof. No hypothesis of a downstream theorem is used to define
its own maps.

### Edge cases

Checked identity inclusions A=B, repeated stages in a tower and the multiplication
unit; arbitrary ramified inclusions use completed ring change and no common exponent.
Checked f=id and empty X: all maps remain the specified mates/counits and empty points
produce a zero target. Nonreduced finite fibres use all maps from Spec(k), not an
assumption that the fibre is reduced or a disjoint union of points. No nonempty fibre
hypothesis is present. The zero object is allowed at every vertex. Finite-data lists
allow n=m=t=e=0, and any mixture of empty lists; all witnesses are chosen at a single
stage. Both standard halves and all integers are quantified; no restriction to the
heart is substituted for t-exactness. Scheme universe and closure universe are
independent. Every delivered module disables both autoImplicit and relaxedAutoImplicit.

### Searches and source reading

Read the full item, every statement dependency and its recorded signature/docstring,
and the current blueprint opening finite-stalk/exactness step. Read Bhatt--Scholze
Proposition 6.8.14(1),(2) and Remark 6.8.15 in the obtained local text. Its colimit and
rationalization are the coefficient conventions used here; the diagram normalization
is the counit construction spelled out by the node's eight-step proof.

Initial msearch LeanFinder query: “Finite coefficient extension commutes with finite
direct image and pullback and counit restriction and descends to common stage
categories” returned eight unrelated condensed/profinite results. Loogle
`"extensionOfScalars", "pushforward"` returned zero hits. Mathlib grep
`extensionOfScalars.*pushforward|pushforward.*extensionOfScalars|changeOfRings`
in Algebra/Category/ModuleCat returned ordinary change-of-rings files, not this
statement. Project/Sheaf and exact-id searches did not find this statement.

For EACH new definition node, the logged LeanSearch query was “Normalized integral
strict coefficient system finite fibre exchange restriction diagram”: eight scheme
normalization/normality results, no match. The logged LeanFinder query was “Coherent
coefficient descent diagram for finite proetale direct image pullback and point
restriction”: eight `ExistsHomHomCompEqCompAux` results, no match. The logged Mathlib
CategoryTheory grep `finiteRestriction|coefficient.*[Dd]escent|[Dd]escent.*coefficient`
had no hits. The node records retain the actual result names and search dates.
Direct DAG, WeilConjectures and Sheaf searches for finite restriction diagrams,
`IntegralDiagram`, `FiniteData` and geometric comparisons found existing building
blocks but no such packaged notion. `tools/blueprint_refs.py search 'coefficient descent'`
returned no blueprint nodes; `ancestor` gave `lem-zl-finite-pushforward`.

## New nodes

- `def-zl-finite-restriction-integral-diagram`, module
  `Sheaf.Paper.FiniteRestrictionCoefficientCore`: three actual strict-system
  functors and arrows, their constructible restrictions, integral comparisons,
  unit/arrow laws and balanced tower equation.
- `def-zl-finite-restriction-geometric-comparisons`, module
  `Sheaf.Paper.FiniteRestrictionCoefficientGeometry`: actual completed pullbacks,
  their normalized integral/raw rational scalar comparisons, existing strict-image
  comparisons, geometric endpoints and the finite target fan.
- `def-zl-finite-restriction-normalization`, module
  `Sheaf.Paper.FiniteRestrictionCoefficientNormalization`: projection-normalized
  ordinary/tower agreement, endpoint scalar equations and literal tensor counit formula.
- `def-zl-finite-restriction-finite-data`, module
  `Sheaf.Paper.FiniteRestrictionCoefficientFiniteData`: simultaneous finite-stage
  representatives and conditional t-exactness/exact-heart descent predicates.

Each is a definition node with no postponed proof, complete search records, a source
and blueprint ancestry, and one owning module. The item retains its original natural
language statement and gains only these statement dependencies and its Lean record.

- `def-zl-finite-restriction-geometric-arrows`, module
  `Sheaf.Paper.FiniteRestrictionGeometricArrows`: ordinary representative-normalized
  adjunction, pasting and identity data; their completion-unit-normalized geometric
  mate and point-counit maps; equality with both transported strict arrows. Added
  for H3 of returned immutable head 46406013e064. Searches: LeanSearch found generic
  derived units/counits and mateEquiv; LeanFinder found generic derived adjunctions
  and pullback-shift formulas; Mathlib CategoryTheory grep for completed exchange or
  completion counit had zero hits. Direct DAG, Sheaf and WeilConjectures searches
  found general geometric constructions, not this intrinsic finite-fibre arrow
  datum. Blueprint search 'finite restriction geometric arrows' had zero nodes.
  All three service queries and their actual result names are recorded in the node.

## Validation

Every delivered file is checked with the prescribed server scompile.py, against the
live published library and the supplied sibling overlay, one file at a time. No
library or global build is run. The delivery wrapper performs the server preflight
and repeats the per-file checks before push. The expected theorem `sorry` is the only
permitted warning; style warnings are repaired before delivery.

## Repair of returned head 46406013e064

The current main item and the retained delivery were compared before this repair:
the original natural-language statement and hypotheses remain unchanged. The repair
changes the main Lean signature, adds its geometric-arrow definition dependency, and
adds the point-sections theorem to statement dependencies. No upstream file is edited.
The four previous helper definitions retain their statements and implementations.

1. **H3, actual geometric arrows.** The returned `Endpoints` data allowed simultaneous
   negation of its middle isomorphism and point projections without changing the
   scalar equations. Scalar normalization therefore did not pin the transported
   exchange. The repair takes the return's alternative of stating the arrows on the
   geometric composites. The new module `Sheaf.Paper.FiniteRestrictionGeometricArrows`
   defines `GeometricArrows.exchange` by `mateEquiv` of completed adjunctions and the
   completed square; `GeometricArrows.component` pulls the h-counit along i_x and uses
   the h i_x=id and v i_x=x compositors. These definitions have real data and contain
   no postponed theorem. They are not defined by transporting through N.

   `OrdinaryAdjunction.Normalized` pins the ordinary pushforward comparison to the
   identity section map and its derived Hom bijection by the actual ordinary cochain
   adjunct, universal pullback counit and right-derived cochain unit. In particular
   an arbitrary adjunction with the same two functors cannot supply a different
   counit. `OrdinaryComposition.Normalized` fixes direct-image pasting by the actual
   fibre-product section restriction, takes its ordinary inverse-image conjugate,
   and pins its derived comparison on every flat-term K-flat representative by the
   universal cochain counits. `OrdinaryIdentity.Normalized` does the same for the
   identity fibre product. These formulas use the actual small pro-etale site
   `MorphismProperty.Over @WeaklyEtale ⊤`.

   `CompletedAdjunctionNormalized` fixes each completed adjunction unit to the
   ordinary derived unit followed by direct image of the canonical
   `ordinaryIntegralCompletionComparison` and the existing
   `IntegralModel.reconstruction`. An adjunction's unit fixes its counit. The cited
   completion comparison is itself uniquely normalized by
   `integralDerivedPullbackComparison` on every flat-term K-flat complex: its chain
   model is the quotient augmentation with zero second Roos coordinate. The retained
   reconstruction already has `IntegralModel.realization` and its augmentation
   normalization. The repair therefore uses the existing representative pins; it
   does not introduce a new arbitrary strict-to-completed identification.

   `GeometricArrows.SquareNormalized` and `.PointNormalized` require that precomposing
   the completed square and point compositors by the two canonical completion maps
   gives the ordinary normalized square, respectively the normalized point identities.
   Thus these geometric maps cannot be sign-changed while keeping their laws.
   `GeometricArrows.Normalized` collects all these equations for every coefficient
   stage. The theorem now returns `J : GeometricArrows ...` with this predicate.

   Finally `Endpoints.ArrowsNormalized` asserts the two actual equalities
   `N.source.inv ≫ I.exchange ≫ N.middle.hom = J.exchange` and, for every x,
   `N.middle.inv ≫ I.restriction ≫ N.projection x = J.component x`.
   The theorem explicitly requires this predicate. The reviewer's simultaneous
   middle/projection sign change negates the first left-hand side and leaves the
   geometrically fixed right-hand side unchanged, so it no longer satisfies the
   statement. The second equality ties every target projection to the actual
   geometric counit, while the existing fan still covers the empty fibre case.
   Rational and point-section clauses apply to these same actual integral arrows
   by the existing localization and naturality pins. The proof docstring now states
   the ordinary-representative and completed-mate comparison step explicitly.

2. **H2, point-sections ownership.** Added the landed theorem node
   `lem-weil-point-sections-scalar-extension` directly to the item's `stmt_deps`.
   `SectionsCompatible` continues to use its recorded `pointSectionsScalarExtensionIso`
   and `pointIntegralConstructible_iff`; neither is replaced or copied. Its original
   `proof_deps` entry remains. This is the explicit dependency repair requested by
   the return, not a claim that those declarations are independent definitions.

Additional dependency declarations read for the repair:
`Sheaf.Paper.OrdinaryCompletedIntegralPullback` supplies
`ordinaryIntegralModulePush`, `ordinaryIntegralModulePull`,
`ordinaryIntegralModuleAdjunction`, `ordinaryIntegralDerivedPull`,
`ordinaryIntegralPullComplexCounit`, `ordinaryIntegralCompletionComparison` and its
unique good-representative normalization. `Sheaf.Paper.SfStrictDirectImageScalarComparison`
supplies the existing `IntegralModel.realization`, `.reconstruction` and
`.reconstruction_normalization`. `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
supplies the ordinary cochain adjunction; Mathlib supplies `mateEquiv` and
`conjugateIsoEquiv`. No new hypothesis on f, the fibre or coefficient extensions is added.

Repair edge checks: the identity compositor is explicitly section-normalized;
nonreduced and empty fibres retain the original `Points`, fan and zero clause; the
point laws quantify over every x and are vacuous for an empty fibre. No comparison
is inferred merely from its reductions. The geometric arrow equalities are whole
derived-map equalities, and include the sign counterexample as a diagnostic test.
The closure universe v and scheme universe u remain independent.

Repair validation: all six delivered modules compile separately through scompile.py
against the live server library and sibling overlay. There are no errors or warnings.
The main theorem remains the only `sorry`. The report's earlier statement that there
were only four new definition nodes is superseded by the additional node below.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
