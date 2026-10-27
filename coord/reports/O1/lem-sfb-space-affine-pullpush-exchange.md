## Worker report

The delivery states `lem-sfb-space-affine-pullpush-exchange` in
`Sheaf.AlgebraicGeometry.SpaceAffinePullPushExchange`. The item is represented by
the complete declaration family in `lean.declarations`, with
`AlgebraicGeometry.AlgebraicSpace.affine_pullpush_exchange` as its main declaration.
The four theorem bodies are `sorry`; the seven definitions have concrete data.
No mathematical statement or proof step of the DAG node is changed. Six already
landed definition dependencies are added to cite the canonical constructions used.

Source checked: `literature/stacks-project/spaces-perfect.tex`,
`lemma-affine-morphism-pull-push` (Tag 08IJ), lines 768--798, and
`lemma-compare-base-change` (Tag 08IR), lines 4863--4923. The first source constructs
the precise counit-normalized pull-push arrow. The second identifies the pushed
exchange before its Tor-independence argument. The current blueprint ancestry was
checked in `literature/blueprint/latest/blueprint/sec-six-functors-basics/` under
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`; this is a
supporting input, not a change to the unit's statement or route.

Hypothesis and clause correspondence:

- The base scheme and spaces over it are `{S : Scheme.{u}}` and
  `{X Y X' Y' : AlgebraicSpace S}`. Morphisms `f`, `g`, `h`, `f'` have exactly the
  displayed domains and codomains. The coefficient rings are the structure sheaves.
- The size convention is implemented by explicit universes `u w` and separate
  `[HasDerivedCategory.{w} Z.SmallModules]` instances for the participating spaces.
  `SmallModules` uses the existing equivalent small affine model of the small
  étale ringed topos; there is no assumption quantifying over all spaces' derived
  categories, no equality imposed on site universes, and no new abelian structure.
- For each arbitrary affine `a`, representability is `IsRepresentable a.hom.hom`
  and affine scheme tests are `MapIsAffine a`. These two hypotheses together give
  exactly the node's stated meaning of affine, also for the final map `g`.
- `affinePullPushAlgebra a` is literally `(moduleDirectImage a).obj O_X` on the
  original site. `affinePullPushSingle Y M` is its actual restriction to the small
  model followed by `DerivedCategory.singleFunctor _ 0`, giving `M[0]`.
- `affinePullPushAlpha` is the canonical map from the ordinary structure image in
  degree zero to the unbounded derived image. It uses the actual restriction
  equivalence's unit, `spaceRightDerivedComplexUnit`, the single-complex comparison,
  and `smallModuleUnitIso` to identify the restricted structure module. No arbitrary
  map or isomorphism is supplied as input. `affine_pullpush_normalized` asserts
  quasi-coherence of the algebra, `IsIso` of alpha, and `IsIso` of lambda for each
  `F` with `Y.derivedQCohProperty F`.
- `affinePullPushLambda` is precisely the adjoint under `spaceDerivedAdjunction a`
  of the tensor pullback comparison, `1` tensor pullback of alpha followed by the
  derived counit at `X.derivedStructure`, and the scalar right unitor. This spells
  out the source's identification of ordinary and derived structure images, so
  the definition needs no chosen inverse or invertibility hypothesis.
- Naturality in `F` is `affinePullPushLambda_naturality`: tensoring a morphism
  `q : F ⟶ G` with the identity on the coefficient, then lambda at `G`, equals
  lambda at `F` followed by `Ra_*La^*q`. The two QCoh hypotheses say the morphism
  is in exactly the full subcategory used by the node.
- The fibre product is expressed by `sq : IsPullback h f' f g`, retaining both
  projections. This allows any realization of the specified fibre product.
- `affinePullPushOrdinaryCoefficient` is the canonical ordinary base-change map
  with roles `(g,f,f',h)`, applied to `O_Y'`, followed by direct image of the
  ordinary structure evaluation for `f'`. The evaluation is the adjoint of the
  existing regular-function `moduleStructureMap f'`. Its invertibility, the
  identification `f^* A ≅ B` in the node, is stated separately as
  `affinePullPushOrdinaryCoefficient_isIso` under exactly affine `g` and the square.
- `affinePullPushCoefficient` is `c`: the universal left-derived counit on the
  degree-zero restricted algebra, followed by the single-complex comparison,
  the existing `smallRestrictionPullback`, and restriction of the preceding
  ordinary base-change identification. It never inverts the derived-to-ordinary
  augmentation. All complexes here are formed on the already existing small
  model; the first failed compile's original-site zero-object issue was removed
  without adding a hypothesis.
- `E : X.DerivedModules`, `hE : X.derivedQCohProperty E`, and
  `hfE : Y.derivedQCohProperty ((derivedDirectImage f).obj E)` are exactly the
  two QCoh conditions of the final clause. There is no boundedness condition.
- The projection morphism is the existing `derivedProjectionFormulaMate` with
  `spaceDerivedPullback f`, `derivedDirectImage f`, their canonical adjunction,
  the two existing derived tensor functors, and `moduleDerivedPullbackTensor f`.
  Thus its transpose is tensor comparison followed by the f-counit on the first
  factor, as required by `lem-weil-pbc-ringed-projection-mate-exact`.
- The exchange is the existing `moduleDerivedExchange f f' g h sq.w E`, whose
  complete definition was read: it is the adjoint of pullback-composition followed
  by `Lh^*` of the f-counit. It is not redefined here.
- `affinePullPushDirectImageSquare` is the exact comparison
  `Rg_*Rf'_* ≅ Rf_*Rh_*`, composed from
  `spaceDerivedChartDirectImageComp`, equality of the composites, and the inverse
  comparison on the other path. Those compositors are the recorded right-adjoint
  conjugates, so this fixes the normalization in the displayed equality.
- Lean's `≫` reads left to right. The left side of `affine_pullpush_exchange` is
  lambda at `(g,Rf_*E)`, then `Rg_*` of exchange, then the preceding composition
  comparison. The right side is the projection mate, then `Rf_*` of `1_E` tensor
  `c`, then `Rf_*` of lambda at `(h,E)`. These are exactly the two node arrows
  into `Rf_*Rh_*Lh^*E`. No `IsIso` hypothesis or conclusion occurs for `c`, the
  projection morphism or exchange. No flatness, Tor independence, properness,
  quasi-compactness, separation, Noetherian or finite-presentation hypothesis is
  imposed on `f`; affineness of `g` and the two QCoh conditions are retained.

Dependency declarations read and used (names in the
`AlgebraicGeometry.AlgebraicSpace` namespace unless otherwise specified):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentable`,
  `structureSheaf`, `Modules`; and
  `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `singleFunctor` and
  `singleFunctorIsoCompQ`. The size dependency is the recorded convention,
  with no declaration to import; explicit universes implement it here.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the
  inherited `SheafOfModules.IsQuasicoherent`, with its slice instances.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`, and
  `moduleTensorAdjunction`; their full chart-limit and adjunction definitions
  were read, so the images and evaluations retain the specified normalization.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, and the categorical `IsPullback` interface.
- `Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus`:
  `space_derived_etale_chart_calculus`, `spaceDerivedChartDirectImageComp` and
  the composition unit/counit equations. Its publicly imported
  `SpaceAffineHomComparison` supplies `spaceDerivedAdjunction` and
  `spaceRightDerivedComplexUnit`; `SpaceDerivedPullback` supplies
  `spaceDerivedPullback` and its universal counit.
- `Sheaf.AlgebraicGeometry.SpaceAffineModuleBaseChange`:
  `affine_moduleDirectImage_baseChange`; the public ordinary comparison is
  `moduleBaseChange` from `SpaceFlatDirectImageBaseChange`.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact`,
  including its equality with the canonical `CategoryTheory.derivedProjectionFormulaMate`
  declared in its public import `Sheaf.Paper.ProjectionFormulaArrows`.
- Added existing dependencies: `def-sfb-space-base-change-comparisons` uses
  `SpaceDerivedModuleOperations.moduleDerivedPullbackTensor` and
  `smallRestrictionPullback`; `def-sfb-space-module-derived-exchange` uses
  `SpaceModuleDerivedExchange.moduleDerivedExchange`;
  `def-sfb-space-affine-sections-compositors` uses
  `SpaceAffineSectionsCompositors.smallModuleUnitIso`;
  `def-sfb-space-module-structure-map` uses
  `AlgebraicSpaceModuleStructureMap.moduleStructureMap`;
  `def-sfb-space-affine-quasifinite-properties` uses
  `AlgebraicSpaceAffineQuasiFinite.MapIsAffine`;
  `def-sfb-space-derived-module-calculus` uses
  `AlgebraicSpaceDerivedModules.derivedQCohProperty`, `derivedDirectImage`,
  `derivedStructure`, `SmallModules` and `derivedDualityModel`.
  These were all already recorded on the base and are reused unchanged.

All recorded modules for the already stated proof dependencies are imported,
with ordinary `import` when only the proof uses them. The two proof dependencies
`lem-sfb-space-affine-locality` and
`lem-sfb-space-affine-derived-pushforward-conservative` currently have no recorded
declaration, so have no proof import to add. No missing statement prerequisite
remains. No additional node or dependency-module repair was needed.

Edge cases checked mathematically before drafting and again against the final file:

- Empty source or target and zero complexes are allowed; no nonempty, connected,
  nonzero, faithful, positive-rank or point-existence hypotheses appear.
- Identity morphisms and all identity squares remain included. The structure
  evaluation is multiplication and the compositor is adjunction normalized.
- Unbounded complexes and infinite-rank quasi-coherent modules are allowed.
  `derivedQCohProperty` quantifies over every integer degree.
- For the nonflat affine map `Spec F_2 → Spec Z`, the ordinary structure image
  comparison and lambda remain isomorphisms, while the counit augmentation
  `F_2 tensor_Z^L F_2 → F_2` need not be. The lambda proof docstring explicitly
  keeps this augmentation rather than treating it as invertible.
- In a self-intersection square over `Spec Z`, the coefficient c may have a
  nonzero negative Tor contribution. The final equality permits this; neither
  coefficient c nor exchange is declared invertible.
- No independent smaller test-scheme universe and no universal derived-category
  instance is assumed. Separate localizations in arbitrary common size `w`
  match the recorded small-model interfaces.

Searches performed with the prescribed `msearch.py O1
lem-sfb-space-affine-pullpush-exchange` wrapper:

- `leanfinder`: "Affine algebraic space derived pullback pushforward tensor
  structure algebra counit normalized projection exchange". Eight hits, including
  `AffineSpace.over_over`, `Scheme.Pullback.ofPointTensor_SpecTensorTo_assoc`,
  `Triplet.specTensorTo_snd/fst` and affine scheme tensor-pullback formulas;
  none states the unbounded algebraic-space assertion or the normalized equality.
- `loogle`: `"pullback", "pushforward"`. Twelve hits: ordinary presheaf module
  adjunctions and sieve pullback/pushforward relations; no exact theorem.
- Mathlib `grep`: `affine.*pull.*push|projectionFormula|derivedProjection`.
  Zero hits; no existing statement.
- `leansearch`: "Affine morphism derived pull push quasi coherent tensor
  structure algebra". Eight hits, including `IsAffineHom`, `isAffineHom_iff`,
  affine base-change permanence and ordinary scheme module adjunctions; no match.
- `rg -n` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `affine.*pull.*push|affinePullPush|derivedProjectionFormulaMate` and the item id.
  The general projection mate exists and is reused. The stronger flat/qcqs
  projection-formula node is a different assertion. The existing exchange,
  two-space tensor comparison and small-model unit are reused. The specialized
  structure alpha below the relatively flat closed-kernel theorem confirms the
  generic right-derived-unit construction; that downstream theorem is not an
  import prerequisite. No existing declaration states this node.
- Exact-name `rg` in Mathlib/project sources and `dag/lean_names_upstream.json`
  found no collision with any of the eleven delivered declaration names.

No STATEMENT-DISPUTED issue or node statement correction was needed. Every helper
belongs to an object or arrow explicitly named in this node, and every postponed
theorem is a clause of this node with its source and complete proof docstring.

## Second reading by O1

The dispatcher explicitly assigns a single worker and forbids starting other
agents. This section records that worker's second pass with the node and final
Lean file open; the maintainer performs the independent review of the delivery.

I checked the normalizations rather than only comparing object types. Alpha begins
with the actual module-equivalence unit and ends with the inverse restriction
of O. Lambda transposes tensor comparison followed by `1 tensor (La^*alpha;
epsilon)` and the scalar right unitor; it does not use an arbitrary isomorphism
between its source and target. Ordinary coefficient base change swaps the roles
of f and g and uses `sq.symm`; the exchange retains their original roles and
uses `sq.w`. I checked the compositor's direction from `Rg_*Rf'_*` to
`Rf_*Rh_*`, including the equality `sq.symm` between composite arrows. The final
target is `Rf_*Rh_*Lh^*E` on both sides. The projection mate puts E in the first
tensor factor and the coefficient in the second, agreeing with the node.

The second pass added an explicit theorem for invertibility of the ordinary
coefficient identification, so that the word "identification" in the node is
represented as well as its canonical map. The four separate localization
instances and the two QCoh assumptions remain exactly as required. I checked
that no original-site single complex, Tor-independence assumption, bound on E,
qcqs assumption on f, or invertibility assertion for c/projection/exchange was
introduced. The helper definitions introduce no new choice. All declarations
and their intended ownership are included in `lean.declarations`.
