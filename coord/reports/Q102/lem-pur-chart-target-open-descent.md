## Worker report

Item: `lem-pur-chart-target-open-descent`. Module:
`Sheaf.Paper.ChartTargetOpenDescent`. Main declaration:
`WeilConjectures.PurityFiniteSetting.chartTargetOpenDescent`.

The delivery states both restriction formulas and the cover equality test. It uses
real definitions for T, Q, their source and Tate comparisons, the affine integration
transpose, and all conclusion predicates. Every new theorem has whole proof `sorry`.
No node statement, proof plan, or proof dependency is changed. The statement dependencies gain the new definition node
`def-pur-chart-diagonal-assembly-data`, which owns abbreviations of the published
canonical maps and geometry dictionary. The two theorem nodes previously added
to statement dependencies have been removed in response to returned H2.

Hypotheses and objects, clause by clause:

- The finite field k, its algebraic closure, the prime ell different from p,
  the actual quotient coefficient ring, and positive n are the fields of
  `PurityFiniteSetting`. `_hE : P.extension = ⊥` specializes E to Q_ell.
  `P.Coefficient` is the existing universe lift of the same quotient, not new
  coefficient data. The exponent `P.diagonalExponent = ell^n` annihilates it.
- `X Y : Scheme.{u}`, `aY`, `[LocallyOfFiniteType aY] [QuasiCompact aY]` and
  the same finite-type instances on f give the finite-type k-schemes. The
  structure of X is f followed by aY, so f is a k-morphism without an extra
  compatibility premise. `[IsSeparated f] [SmoothOfRelativeDimension d f]`
  and `d : ℕ` express the relative separatedness, smoothness, pure dimension,
  and d >= 0. No `[IsSeparated aY]` appears.
- `U : X.Opens` and `U.ι` express the open immersion. Using opens loses no
  arbitrary open immersion, which is canonically isomorphic to its image.
- `e : U.toScheme ⟶ affineTraceTower Y d`, `[Etale e]`, and `w` express
  the coordinate chart over Y. This is the published ordered affine-space
  model, with the canonical `affineTraceAffineSpaceIso Y d` to Mathlib's
  `AffineSpace (ULift (Fin d)) Y`. This model retains the original coordinate
  order; at d=0 its projection is literally the identity.
- The exceptional object is the existing `diagonalDualizing f` and the fixed
  finite exceptional functor `sfFiniteExceptionalAt`, through
  `diagonalDualizingComparison`. Pullback is the actual pro-etale
  `upperStar ... .leftDerivedFunctor`. These are the dependency's transported
  finite exceptional image and derived pullback, not abstract functor inputs.
- `chartTargetT` is derived restriction of `diagonalDualizingObject`, followed
  by `chartTargetTate` to put its target in the canonical coordinates L.
- `chartTargetGamma` is `asIso` of the existing `diagonalAffineMate`, which
  transposes the actual ordered affine trace counit. The helper
  `chartTargetAffineMate_isIso` states vector purity on the full nonseparated
  base domain. No arbitrary isomorphism or bare Nonempty choice defines Gamma.
  Vector integration is defined by its unique chartwise specified traces; on
  its trivial frame the actual trace is this affine counit. On separated
  opens `ordered_integration_transposes` identifies its transpose with Gamma.
- `chartTargetQ` composes the canonical source restriction,
  exceptional-composite congruence, inverse etale locality, pullback of
  `chartTargetGamma.symm`, and canonical Tate restriction. Its ordinary
  presentation is transported by the actual comparison functor. Thus all its
  comparison units are retained. `t`, `D`, `N` are universally quantified
  normalized root-line/projective-adjunction/compact-support presentations,
  not additional purity or orientation assumptions.
- `ChartTargetDiagonalRestriction` quantifies every affine open V of Y.
  Its source is `((U.ι ≫ f) ⁻¹ᵁ V.1).toScheme = U_V`; its restricted map is
  `(U.ι ≫ f) ∣_ V.1`. It equates the restricted T (followed by Tate
  restriction) with canonical `chartTargetSource`, `chartTargetBase`, then
  `chartDiagonalAssembly`. The last is literally alpha inverse, normalized
  delta, beta from the published chart module. `chartTargetGeometry`
  supplies its geometry dictionary; the predicate quantifies all dictionaries,
  whose fields are proof-irrelevant propositions, rather than assuming new
  geometric hypotheses.
- `ChartTargetCoordinateRestriction` uses the same U_V, source comparison and
  target-open exceptional mate. It equates the restricted Q with
  `chartTargetCoordinate` at eV. The canonical affine target change is
  `affineTraceMap V.1.ι d`; the two `IsPullback` certificates say precisely
  that pV and eV are the restrictions. `chartTargetRestrictedChart` states
  existence of these certificates and eV, with etaleness and the over-V
  equation as conclusions. The local coordinate map is exceptional/etale
  composition followed by eV pullback of the inverse actual integration mate.
- `ChartTargetTraceRestriction` writes out the actual affine trace equation:
  compact-support exchange, right-functor Tate base change, constant coefficient
  comparison, and local trace equals pullback of the global trace. It is the
  ordered-adjunction presentation of `t_(p_V) C_(d,v) = v* t_p`.
- `ChartTargetSheafTest` uses the actual `chartTargetSheaf = Lambda_U(d)`.
  An isomorphism from L[-2d] to its degree-zero single complex and fullness
  give a unique ordinary endomorphism for every a after T inverse and shift.
  The next clause spells out commutation with exact ordinary restriction
  using `mapDerivedCategorySingleFunctor`. The third clause is equivalence
  of equality for a,b and their corresponding ordinary maps; the last is
  detection of ordinary maps on every affine-target inverse-image cover.
  The isomorphism is existential conclusion data; no object is defined by
  a choice from an unproved mere-existence statement.
- `ChartTargetEqualityTest` is exactly the displayed implication for T,Q,
  for every `I : Type v`, every affine family `V`, and `iSup V = ⊤`.
  It compares the actual restricted arrows before any chosen identification.
  All source/target comparisons used in the formulas are invertible, so
  this is the same equality test as after the canonical identifications.

Recorded dependencies read and reused (the directly used finite declarations are
listed when the primary record also covers other coefficient stages):

| Node/interface | Module and declarations |
|---|---|
| def-pur-conventions | `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `Ring`, `Coefficient` |
| def-weil-open-immersion | `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, scheme open inclusion |
| def-weil-exceptional-inverse-image | `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: `ConstructibleExceptionalCoefficients.System`; finite `ProEtale.sfFiniteExceptionalAt` reexport |
| def-weil-derived-pullback-tensor-hom | `Sheaf.Paper.DerivedPullbackTensorHom`: finite derived pullback, with its fixed-ring `ProEtale.upperStar` presentation |
| def-pur-section-invariant | `Sheaf.Paper.PuritySectionInvariantIntrinsic`: `sectionInvariantFinite`; DNC source comparison identifies its fixed-ring presentation |
| thm-pur-diagonal-dualizing-object | `Sheaf.Paper.PurityDiagonalDualizingObject`: `diagonalDualizingObject`, `diagonalDualizingComparison`, `diagonalEtaleLocality`, `diagonalAffineMate` |
| def-coefficient-twists-detailed | `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`; its published `FixedFinitePositiveCoefficientTwist` presentation `diagonalTwist`, `diagonalTwistEtale` |
| lem-pur-projection-purity-agreement | `Sheaf.Paper.ProjectionPurityAgreement`: `projection_purity_agreement` and published chart Gamma interface |
| lem-pur-diagonal-base-change | `Sheaf.Paper.PurityDiagonalBaseChangeCompared`: `comparedDiagonalBaseChange` |
| thm-pur-dnc-invariance | `Sheaf.Paper.PurityDncInvariance`: `Dnc.existsUnique_dncInvariance`, `Dnc.pullComparison` |
| cor-pur-vector-bundle-purity | `Sheaf.Paper.VectorBundlePurity`: `vectorBundlePurity` |
| thm-pur-cohomological-smoothness | `Sheaf.Paper.CohomologicalSmoothnessTheorem`: `isCohomologicallySmooth_of_smooth` and canonical smooth exceptional base-change mate |
| lem-amb-affine-space-top-trace | `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`: `exists_affineSpaceTopTrace`, actual `affineTraceCounit` and base-change maps |
| lem-pur-vector-integration-site-comparison | `Sheaf.Paper.VectorIntegrationSiteComparison`: `finiteTypeSiteComparison`, `vectorIntegrationSiteComparison`, `vectorTensorComparison` |
| lem-weil-pbc-derived-single-fully-faithful | `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`: full and faithful instances on `singleFunctor` |
| lem-weil-proetale-weakly-etale-localization | `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`: `Scheme.ProEt.weaklyEtale_localization` |
| lem-pur-sheaf-hom-cover-gluing | `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`: `SheafOfModules.existsUnique_hom_of_cover` |
| def-weil-scheme-morphism-properties | Convention-only pointer node: Mathlib `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension` |
| def-weil-etale-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` |
| def-sbc-affine-space | `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`; existing ordered coordinate isomorphism |
| def-amb-vector-integration | `Sheaf.AlgebraicGeometry.VectorBundleIntegration`: `vectorBundleIntegration`, its uniquely normalized chart trace |
| lem-pur-affine-ordered-integration-transposes | `Sheaf.Paper.AffineOrderedIntegrationTransposes`: `ordered_integration_transposes` |
| chart definition interface | `Sheaf.Paper.ChartDiagonalAssemblyData`: `chartDiagonalAssemblyData`, `chartOrdinaryBaseChangeData`, `ChartAffineDiagonalGeometryData`; abbreviations of the published definitions |

The proof imports also include the chart-domain, exact localized restriction,
dualizing-cocycle and finite-etale normalization modules. No imported dependency
is replaced by a private copy. The retired Sheaf HomCoverGluing module is avoided;
the node's recorded upstream module is used.

Edge cases checked: d=0 (identity tower, zero shift, zero-fold root tensor), empty
U, empty Y and its empty cover, arbitrary affine covers including infinite and
empty index types, positive n=1, no ramification-divisibility restriction,
nonseparated X or Y, and arbitrary target overlaps (never assumed affine).
The small pro-etale site retains object universe u+1, morphism universe u,
and coefficients in u+1; the cover index universe v is independent.

Searches made before writing, all through the prescribed tools:

- `msearch.py ... leanfinder "Diagonal and coordinate purity orientations restrict
  to affine target opens and equality is detected by sheaf endomorphisms"`:
  8 hits on scheme diagonal-locality properties; no orientation statement.
- `msearch.py ... loogle "CategoryTheory.Functor.map_injective, CategoryTheory.Sheaf.hom_ext"`:
  0 hits.
- `msearch.py ... grep "purity.*restrict|orientation.*restrict|hom_ext" AlgebraicGeometry`:
  25 hits, principally scheme and sheaf extensionality; none states this node.
- `msearch.py ... leansearch "derived category shifted sheaf endomorphisms equality
  restriction open cover"`: 8 hits on ordinary sheaf conditions and restrictions;
  none gives the two specified purity comparisons.
- `rg` for the node id, target-open descent names, orientations and restrictions
  under both `lean/WeilConjectures` and `lean/Sheaf`: no declaration for this node;
  `DiagonalOrientationCharts` cites this node only in its proof plan. Related
  `DiagonalDncChartNormalization` provides usable canonical factors, reused here.

No statement correction or STATEMENT-DISPUTED issue was found. The current
blueprint source was read from `literature/blueprint/latest/`, Steps 1--4.

## Second reading by Q102

Second pass by the assigned Q102 worker, with the node and final file reopened;
no additional agent was started, as the dispatcher brief prohibits it. This is
not represented as an independent agent review; the maintainer's independent
review remains required.

The second pass checked the three paragraphs of the node against the five
conclusion predicates and each defined map. The coordinate comparison on a
nonseparated base must remain the actual integration transpose; it is the
existing counit mate, never a chosen orientation. The affine and local chart
maps use the canonical ordered-coordinate base change. The formula's source
map uses source-open locality followed by smooth target base change, rather
than a base-change square that would incorrectly omit U. No absolute separated
base instance is introduced. The comparison-unit factors agree with the
published chart interface. The degree-zero test explicitly removes T and the
shift and then uses an ordinary module-sheaf Hom; it does not assert descent
for arbitrary derived Hom. The local square existence helper prevents the
local coordinate formula from being merely conditional on unstated chart data.

Compiler feedback corrected an initial misuse of a field-base Noetherianity
helper on an open inclusion: opens now use the general finite-type
Noetherianity theorem. The source-dependent ordinary maps and all universes
remain explicit. Each new theorem carries its proof plan and this node's
blueprint tag; definitions have real data. Validation results are recorded
below after the final compile and dry run.

The four postponed theorem declarations are `chartTargetAffineMate_isIso`,
`chartTargetGeometry`, `chartTargetRestrictedChart`, and
`chartTargetOpenDescent`; all are attached to this node and its proof plan.
The other thirteen declarations are explicit definitions of the node's maps
or predicates. No hollow data definition or private replacement was introduced.

## New nodes

`def-pur-chart-diagonal-assembly-data` owns `Sheaf.Paper.ChartDiagonalAssemblyData`.
Its three abbreviations re-export the actual `chartDiagonalAssembly`,
`chartOrdinaryBaseChange` and `AffineDiagonalGeometry` definitions. The first
retains every original hypothesis and the alpha-inverse/delta/beta composite;
the second retains the arbitrary Cartesian square and canonical smooth mate;
the third retains every original instance field for the restriction and its
actual self-product. No data is copied and no theorem conclusion is imported
as a hypothesis. Its source is the current blueprint chart proof, Steps 1--4
and target restriction. LeanSearch and LeanFinder found only general diagonal
and smooth-base-change declarations; Mathlib grep found no exact hit. DAG and
project searches located the three published definitions but no definition
node owning them. The existing `def-pur-diagonal-dnc-chart-data` owns different
arrows and does not include these three definitions. Raw search records are
included in the new node. The node cites the definitions and determining
normalizations used in the constructions, including the existing diagonal
chart data node; it does not use either rejected theorem conclusion.

## Repair of H2

Returned immutable head: `0d93766da1b9`. The sole numbered defect H2 was the
use of theorem nodes for plain definitions in the item statement dependencies.
Added the definition node and abbreviation module above and replaced precisely
those two dependencies by its id. The item imports the new module and uses its
three abbreviations; all other Lean text is unchanged. Its mathematical
statement, proof and proof_deps are byte-for-byte unchanged as JSON values.
Comparison with current main before repair showed only the delivered lean
record and added statement dependencies differed. The delivery wrapper rebases
the repaired sandbox on current main.

The assigned worker reread the new node and module together: all three aliases
have exactly their original parameters, universes and instance hypotheses,
with bodies consisting of calls to the published definitions. No new sorry
was introduced. The existing non-vacuity theorem and all restriction and cover
formulas retain definitionally the same types. Edge cases d=0, empty source,
empty target and empty cover therefore retain their previous statements.
Independent review remains with the maintainer, as requested by the dispatcher.

Repair validation: `scompile.py Q102 lem-pur-chart-target-open-descent` on
both delivered modules exited 0, with no Lean errors or warnings. The separate
single-module check also exited 0. The required `deliver2.py --no-push` passed
preflight and compilation (dry-run commit `e67ce8b53ae`, nothing pushed).
The server waited for shared compiler capacity; both modules completed cleanly.

## Repair of H2 at 9625b306a88a

The independent return identified eight missing definition ownership edges.
Added exactly the eight requested landed nodes to the item's `stmt_deps`.
No other item field, new-node field or Lean file was changed in this repair.
In particular, the mathematical statement, proof, proof_deps and lean.statement
remain identical to returned head 9625b306a88a. The earlier abbreviation-module
repair remains intact. Comparison with current main is handled by the delivery
wrapper; the current item was also read before the edit.

Read each added node's statement and lean record and the following published
signatures and docstrings; these existing declarations are the ones used by
the unchanged item module:

| Added definition node | Published module and declarations used |
| --- | --- |
| `def-amb-affine-trace-tower` | `Sheaf.AlgebraicGeometry.AffineTraceTower`: `affineTraceTower`, `affineTraceProjection`, `affineTraceMap`, `affineTraceNoetherian`, `affineTraceInvertible`, `affineTracePullbackInvertible` |
| `def-amb-affine-trace-construction` | `Sheaf.AlgebraicGeometry.AffineTraceConstruction`: `affineTraceExchange`, `affineTraceRight`, `affineTraceRightBaseChange`, `affineTraceLeft`, `affineTraceCounit` |
| `def-asd-ordinary-finite-p1-arrows` | `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows`: `OrdinaryFiniteTwistTransport`, `ordinaryFinitePullback`, `ordinaryFiniteUnitPullback` |
| `def-asd-ordinary-finite-p1-kummer-class` | `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`: `ordinaryFiniteUnit` |
| `def-asd-ordinary-finite-p1-data` | `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data`: `OrdinaryFiniteP1Datum` |
| `def-amb-vector-integration-charts` | `Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts`: `vectorIntegrationBaseCoefficientPullback` |
| `def-asd-finite-etale-tate-sheaf` | `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf`: `finiteEtaleTateSheaf` |
| `def-sp-etale-compact-support-normalization` | `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`: `EtaleCompactSupportNormalization` |

Second reading by the assigned Q102 worker confirmed that these are definition
ownership edges, with no additional hypotheses or theorem conclusions. The
existing maps, normalization data, formulas, non-vacuity helpers, sheaf and
cover tests, universes and edge cases remain precisely as accepted by the
independent review. No new search or new definition is needed for this repair.

Repair validation: the prescribed `scompile.py` check of both delivered modules
exited 0 with no errors or warnings, reusing the unchanged-source compile results.
