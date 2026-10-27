## Worker report

The delivery states `AlgebraicGeometry.ProEtale.ComponentDerivedSquare.component_derived_pullback_square`
in `Sheaf.Paper.ComponentDerivedPullbackSquare`. Its only postponed theorem is this theorem;
its proof is `sorry`. The helper structures package the witnesses of its simultaneous
existence assertion, with full data and equations. Helper definitions are actual constructions;
the small instance proofs invoke existing preservation/monoidality instances and prove no new
mathematical assertion.

Source read: Hemo--Richarz--Scholbach, the construction immediately before (4.1), PDF pp. 8--9,
and Corollary 4.4(2). The relative construction induces the component map of sites and factors
the structural map to the condensed point. Naturality is the pullback comparison of the
relative test schemes. The w-contractible and henselian hypotheses on the subsequent
Proposition 4.3 and Corollary 4.4 are not hypotheses of that construction or its naturality.
The module docstring and theorem docstring retain the eight-step accepted proof plan.

Hypothesis and clause correspondence:

- Arbitrary affine schemes and maps: `System.corner`, `System.slice`, and `System.square`
  quantify over `X Y : Scheme.{u}`, `[IsAffine X]`, `[IsAffine Y]`, and every `f : Y ⟶ X`.
  The theorem quantifies over the single coefficient input, then supplies all these witnesses
  simultaneously, which permits meaningful identity and composition laws.
- Quotient component spaces and induced map: `affineComponentSpace X` is the recorded actual
  quotient `ConnectedComponents X`, bundled using the spectral-component theorem;
  `affineComponentMap f` is the induced continuous map, not an independent profinite map.
- Small-site universes: `Scheme.{u}`, its `Scheme.ProEt` site, and `Profinite.{u}` slices have
  their actual differing object/morphism universes. Abelian groups and coefficient sections
  are in `u+1`, derived localization is in `u+2` through the existing Grothendieck instances.
  No equality of site object and morphism universes or smaller bound is assumed.
- The profinite slice topology is `(coherentTopology Profinite.{u}).over P`; this is the
  existing finite jointly surjective topology. `sliceDirect h`, `sliceInverse h`, and
  `sliceAdjunction h` are precisely restriction along `Over.pullback h`, its sheafified
  left Kan extension, and their canonical adjunction. Its product order is `E ×_P Q`,
  canonically the symmetry of the source's `Q ×_P E`.
- The component sites use exactly `CondensedRing.componentTests X`, chosen from the
  universal-property-characterized `component_relative_profinite_site`. `Corner.inverse_eq`
  fixes the actual `componentInverse` and `adjunction_eq` fixes its adjunction, including
  the unit. Equalities rather than arbitrary equivalent functors are imposed.
- Arbitrary commutative condensed coefficients: `Λ : Profinite.CondensedRing.{u}` with
  `[IsCommMonObj Λ.X]`. This admits rings without topological or discrete presentations.
  `condensedRingObj Λ.X X` is exactly `(coefficientRing X Λ).X`; profinite coefficients are
  the recorded `profiniteCoefficient Λ.X P`. `Corner.coefficient` and `Slice.coefficient`
  are ring-object isomorphisms with underlying maps `beta.hom.app Λ.X`.
- The structural coefficient comparison is canonical: `Corner.absoluteTests` preserves the
  absolute profinite coordinate (`absolute_coordinate`), and `beta_mate` fixes its direct
  image on every absolute test. The same condition for `Slice.beta` uses
  `Over.starPullbackIsoStar h`. These determine the actual structural comparison by mate
  uniqueness; `Square.coefficient` imposes the full ring-compatible square, not merely
  the existence of some coefficient isomorphism.
- Module sheaves: `Corner.modules`, `Slice.modules` use the existing `mapMod` and restriction
  along the inverse coefficient isomorphism, canonically extension along that isomorphism.
  The scheme edge is the published `CondensedRing.upperStar`. `schemeUnderlying` explicitly
  uses `Mod.extendScalarsIsoComapInv`, so its underlying-sheaf identification is fixed.
  The internal-module encoding is the existing section-module-equivalent presentation of
  `ringedSiteModules`, not a second sheaf-of-modules definition.
- The specified geometric comparison: `Square.tests_eq` identifies its scheme map with
  `component_lift_base_change.choose f` on each relative test; faithfulness of the forgetful
  functor then determines the complete test isomorphism. `Square.abelian_mate` says its
  right mate at `G,E` is `G.obj.map (tests.hom.app E).op`, fixing the direction and the map.
  `Square.ordinary_underlying` determines the actual linear module comparison on all sheaves.
- Exactness: the corner/slice witnesses contain finite-limit and finite-colimit preservation
  of the abelian inverse images; their module instances are inherited from `mapMod` and
  transport along an isomorphism. Additivity is finite-product preservation. The scheme
  pullback uses the published exactness instances. `TensorLift.triangulated` records
  triangulated exactness with the canonical `mapDerivedCategory.CommShift` structure.
- Ordinary unbounded derived categories and ordinary tensor: `Corner.derived` and
  `Slice.derived` are `mapDerivedCategory` of the exact module inverse images. Their
  categories are `Evaluation.D`, i.e. actual unbounded `DerivedCategory (Mod ... ...)`.
  The monoidal structures on these categories are the existing ordinary K-flat derived
  tensor; `TensorLift.symmetric` uses the existing Koszul braidings
  `DerivedCategory.braidedCategory'`, not an arbitrary new braiding.
- The natural isomorphism has exactly the displayed domain/codomain: `leftPath Λ sX f`
  is `π_X^* ⋙ f^*` and `rightPath Λ sY f sh` is `h^* ⋙ π_Y^*`. `Square.theta` is a natural
  isomorphism between them, defined by `mapDerivedCategoryNatIso sq.ordinary` and the two
  canonical `mapDerivedCategoryCompIso` comparisons.
- Termwise localization: this definition uses exactly the existing localization of
  `NatIso.mapHomologicalComplex sq.ordinary`. Its component in degree n is the ordinary
  comparison on `K.X n`, and its chain equation is naturality with `K.d n m`.
  Thus there is no arbitrary derived iso or representatives restricted by boundedness.
- Canonical unit and tensor: `Corner.tensor_canonical`/`unit_canonical` and the analogous
  slice fields fix the abelian inverse-image tensor maps as mates of pointwise restriction.
  Module monoidal structures are the existing relative-tensor `mapMod`/`comap` instances.
  `TensorLift.localization` makes the canonical factorization through Q monoidal relative
  to those termwise structures. `Square.monoidal` writes the tensor equation and the
  coefficient-unit equation explicitly; `System.monoidal` asserts them for every f.
- Identity/composition: `SliceIdentity` and `SliceComposition` fix test isos by projections,
  their abelian adjunction mates, and their underlying module maps. Their derived maps
  are the canonical localizations. `schemeIdentity`/`schemeComposition` use the published
  ordinary scheme pullback comparisons and the existing derived composition maps.
  `System.identity` and `System.composition` give the two complete equations on every K.
- Dualizable restriction: `cornerDuals`, `sliceDuals`, `schemeDuals` preserve the existing
  `IsDualizable`, whose `HasRightDual` witness includes evaluation, coevaluation and both
  triangles. Since the subcategories are full, the fixed theta and its inverse then
  restrict, with the already asserted tensor/unit equations.
- No henselian, w-local, w-contractible, surjectivity, nonempty, discrete, completeness,
  boundedness or finite coefficient hypothesis appears anywhere in the theorem.

Dependencies used (the exact recorded interfaces, read with their docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `IsAffine`.
- `Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`:
  `spectralSpace_connectedComponents_profinite`, through `affineComponentSpace`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.Paper.ComponentRelativeProfiniteSite`: `component_relative_profinite_site`,
  `affineComponentSpace`; their universal mapping property fixes the relative tests.
- `Sheaf.Paper.ComponentLiftBaseChange`: `relativeComponentLift`,
  `relativeComponentCoordinate`, `affineComponentMap`, `component_lift_base_change`.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `upperStarFromPoint`, `condensedPullbackHom`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, through the existing
  `InternalAbelianSheafModule.sectionModuleEquivalence` used by Evaluation's encoding.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`.
- `Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel`: `componentTests`, `componentInverse`,
  `profiniteCoefficient`, `Evaluation.D`. Its already landed owner
  `def-zl-condensed-lisse-evaluation-model` is added to stmt_deps for this reused API.
- `Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`: `profiniteTestProjection`.
  The new existing-definition node `def-zl-profinite-test-projection` is added to
  stmt_deps for the absolute-coordinate normalization. The continuous-realization theorem
  is not a statement dependency; no dependency record is repaired.
- The size-convention node has no Lean object; its requirements are rendered by the explicit
  site/coefficient/derived universes above.

Every already recorded proof dependency module is imported (without public reexport):
`ProEtaleInverseImage`, `SiteInverseImageTensor`, `SiteMorphismComposition`,
`GeometricModuleTransport`, `Sites.GeometricInverseImageExact`, `ExactDerivedComposition`,
`RingedDerivedMonoidalComparisons`, and `ExactFunctorDerivedFunctor`. The Mathlib mate and
localization dependencies enter through their actual imports. No import cycle was needed.

Edge cases checked before writing: empty X and/or Y (the empty profinite slice remains
allowed); identity and composite affine maps (explicit normalization fields); zero ring
(all module operations and equations remain well typed); disconnected spaces and repeated
finite-stage labels (we use the repaired recorded base-change comparison); arbitrary
unbounded complexes (no truncation or resolution hypothesis); non-discrete condensed rings;
and the genuine unequal site object/morphism universes. The exactness hypotheses are
witnesses supplied by the theorem, not additional assumptions on the input schemes.
No STATEMENT-DISPUTED flag and no statement correction is required.

Searches made:

- msearch.py leanfinder: "Naturality of affine connected component site derived pullback
  with condensed ring coefficients" — eight hits, including condensed module naturality
  and generic free-pullback naturality; no geometric component square.
- msearch.py loogle: `SheafOfModules.pullbackComp` — generic pullback composition API;
  no affine-component coefficient-normalized derived square.
- msearch.py grep: `(component|profinite).*(derived|pullback)` — 17 Mathlib hits, generic
  derived naturality or unrelated topology/geometry; no match.
- msearch.py leansearch: "Naturality of relative connected component derived inverse image
  square with condensed coefficients" — eight hits on CatCommSq, dense sites, condensed
  morphism naturality and injective resolutions; none states this result.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for component/derived/pullback combinations,
  `component_lift_base_change`, and the exact item id — the component inverse image and
  w-contractible component compatibility are already present, but neither asserts this
  arbitrary-affine naturality theorem. The latter has a w-contractibility hypothesis and
  an equivalence conclusion; it is not used as the present result.
- Exact namespace search found no `AlgebraicGeometry.ProEtale.ComponentDerivedSquare`
  declarations before writing this file. The new helpers package only this one statement;
  the repair adds an existing-definition node for the reused absolute test projection.

Validation: the complete module passed scompile.py in the sandbox and module positions,
with no errors or non-sorry warnings, within the unchanged 60-second per-file limit.

## New nodes

`def-zl-profinite-test-projection` records the exact existing definition
`AlgebraicGeometry.ProEtale.profiniteTestProjection` in
`Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`; no new Lean module
is written. Its source is HRS Example 3.1, p. 6, with the explicit construction
read at lines 86–94 of the existing module. For every scheme X and profinite S
in universe u, it is the continuous map from |X[S]| to S formed using the first
fibre-product projection and the inverse homeomorphism for the spectrum of
locally constant integer functions. Its definition-node dependencies are the
scheme and the absolute profinite test object. Empty schemes, empty S, finite S,
and non-affine schemes all remain allowed.

LeanSearch and LeanFinder each returned eight general topology/geometry hits,
none defining this projection; Mathlib grep for
`profiniteTestProjection|profiniteToProEtOf` returned zero hits. Project and DAG
searches found the exact existing definition and its helper entry on a theorem
node, but no definition-node owner. `blueprint_refs.py search
profiniteTestProjection` returned zero matches. The new node stores the actual
search results, uses `existing: true`, and does not duplicate the definition.

## Repair of returned delivery

H2 at immutable reviewed head `118950e3f49a`: replaced the added theorem
statement dependency `lem-weil-pbc-condensed-field-continuous-realization` by
`def-zl-profinite-test-projection`. `Corner.absolute_coordinate` uses the plain
projection definition, not a choice from that theorem. The new node binds the
verbatim signature requested by the maintainer. The Lean file stays byte-identical
to the saved reviewed packet. No statement, proof, proof dependency, or existing
dependency record changes. Compared with current main, the item's only changed
fields remain `lean` and `stmt_deps`. The initial saved-packet dry run passed
preflight and compilation at `60e1f555143`; the repaired packet is validated again
below through the prescribed delivery wrapper.

## Second reading by Q117

Repair self-check (no independent worker was started, as the dispatcher forbids
sub-agents): opened the existing projection definition, the new node, the item
record and `Corner.absolute_coordinate`. The binders X : Scheme.{u} and
S : Profinite.{u}, continuous-map codomain, and explicit three-map composite
match the new node clause by clause. The test object is the recorded
`profiniteToProEtOf`, not a private replacement. The projection is data defined
without sorry or a choice from the realization theorem. The item's Lean and its
hypothesis/clause correspondence above remain unchanged, as independently
checked by the maintainer at `118950e3f49a`. The only reported mismatch was the
theorem-node ownership of the definition; the new existing-definition node
and the dependency replacement repair it.

Repaired-packet validation: scompile.py passed both sandbox and library positions
with no errors or non-sorry warnings. The first repaired dry run required the
new-node schema field `import_flags`; supplied its empty list and reran preflight.
