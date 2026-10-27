## Worker report

Item: lem-sfb-filtered-finite-free-projection. Group Q52, stage 2.

The live node is split and has a stage-1 PASS from NR on 2026-10-22, but has no
`lean` or `reviewed_lean` record. That review authorizes statement work; it is not an
existing stage-2 delivery. The preserved sandbox initially contained only dispatcher
brief markers, with no module, node copy, report or delivery result. No earlier push
needed repeating. The earlier worker's “live already split/reviewed” blocker was a
misreading of the stages.

The delivery adds `Sheaf.AlgebraicGeometry.FilteredFiniteFreeProjection` with nine
public declarations in `AlgebraicGeometry.Scheme.FilteredFiniteFreeProjection`:
`source`, `tensorTarget`, `target`, `projection`, `projection_naturality`,
`projectionTransformation`, `strictTensor`, `finiteFreeNormalization`, and
`filteredFiniteFreeProjection`. The three named theorem proofs are `sorry`. All six
definitions have their complete data. In particular projection is the actual adjunct
of the canonical pullback comparison followed by tensoring the counit, not a map
parameter or an existentially chosen projection. The natural transformation uses
exactly these components and the separately named naturality theorem.

The mathematical statement and both dependency lists of the item are unchanged.
No new notion or new node is needed. Two lean-only existing-interface repairs expose
additional declarations already in the recorded dependencies' public-import closures;
see “Dependency modules”.

Hypothesis and clause matching:

- Schemes X and Y and their actual morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  Quasi-compactness and quasi-separatedness are `[QuasiCompact f] [QuasiSeparated f]`
  in the main theorem. The sites are precisely `ProEt.topology X` and
  `ProEt.topology Y`. Their objects have universe u+1 and their arrows universe u.
- R_Y and R_X are the arbitrary ring sheaves R and S, with coefficient universe u+1.
  The binder `c : (proEtaleSheafInverseImage f CommRingCat.{u+1}).obj R ≅ S`
  is the specified cartesian identification. Neither ring is restricted to constant
  coefficients, condensed coefficients, a field, a nonzero ring, or a finite ring.
- Module categories are the recorded `proEtaleRingModules X S` and
  `proEtaleRingModules Y R`. `DerivedCategory` is the ordinary unbounded
  quasi-isomorphism localization, with the standard large localization universe from
  `proEtaleRingModules_hasDerivedCategory`. No completed category is used.
- L and G are the existing `proEtaleRingDerivedPullback f R S c` and
  `proEtaleRingDerivedDirectImage f R S c`. Their adjunction and counit are
  `proEtaleRingDerivedAdjunction f R S c`, induced from the unique ordinary
  tensor-unit-normalized module adjunction. Exact termwise pullback computes L.
- `a : ProEtaleTensorModel Y R` and `b : ProEtaleTensorModel X S` present the
  specified K-flat derived tensors. Their representative isomorphisms compare the
  actual signed total tensor on flat-term K-flat complexes with the supplied tensor
  functor. Thus they introduce no alternative tensor and no arbitrary comparison.
  `proEtaleCanonicalTensorComparison f R S c a b` is selected from the UNIQUE
  comparison characterized on every such pair by the canonical total-tensor square.
- `I : Type (u+1)` and `[SmallCategory I] [IsFiltered I]` render a small nonempty
  filtered category. Mathlib's `IsFiltered` includes nonemptiness, so no case is
  omitted by leaving out a redundant separate `Nonempty I` binder. The index lives
  in the coefficient universe, not an unrelated larger universe.
- `P : I ⥤ proEtaleRingModules Y R` is the diagram. `hP` says for EVERY i there
  is a rank d and an isomorphism `P.obj i ≅ SheafOfModules.free (ULift (Fin d))`.
  `ULift.{u+1}` only places the finite basis in the module universe; it does not
  change its cardinality or exclude d=0. The rank can vary with i and the transition
  maps are unrestricted linear maps.
- `v : Cocone P` and `hv : IsColimit v` supply B=`v.pt` and the ACTUAL legs
  `v.ι.app i`, rather than replacing them by chosen equivalent colimit legs.
- `hB` and `hLB` are `SheafOfModules.IsFlatOnSite` for B and for
  `(proEtaleRingModulePullback f R S c).obj B`. This is the recorded exact-tensor
  definition of flatness. Because pullback is exact, the latter is LB in degree zero.
- The derived input is C, with `hC : ∃ n : ℤ, C.IsGE n`. This is exactly the
  property defining `DerivedCategory.Plus`, with no upper bound or bound on f's
  cohomological dimension. A=GC is written out as the actual derived direct image.
- `source` is P |-> a.tensor(P[0],GC); `tensorTarget` is
  P |-> b.tensor(L(P[0]),C); `target` applies G to that functor.
  `projection` applies the canonical L-adjunction hom equivalence to
  `mu(P[0],GC) ≫ (1 tensor counit_C)`. The coefficient is first throughout, so
  symmetry need not be inserted as a later, unspecified map.
- The main theorem's first conjunct is `IsIso (projection ... v.pt)`, an
  isomorphism of the ACTUAL derived morphism in the ordinary unbounded category.
  Its second conjunct says every finite-stage projection is an isomorphism.
- `finiteFreeNormalization` is stated for EVERY finite free presentation
  `e : free (ULift (Fin d)) ≅ P`, with no chosen basis hidden in a definition.
  It provides unit identifications of source(R_Y) with A and tensorTarget(R_Y)
  with C, under which the actual ring-coefficient mate is the identity. It states
  invertibility of the source and pulled-back tensor finite coproduct comparisons.
  Its displayed equality is
  sigma_source · source(e) · delta_P =
  (direct sum delta_R) · sigma_G · G(sigma_tensorTarget) · target(e).
  These are Mathlib's `sigmaComparison` and `Limits.Sigma.map`, defined by their
  injection composites. After the specified tensor-unit and finite-free
  identifications this is exactly A^{oplus d} -> G(C^{oplus d}). In an additive
  category finite coproducts are biproducts; this formulation avoids introducing a
  second finite-biproduct structure. Rank zero is included by the empty coproduct.
- `projection_naturality` says source(v) ≫ delta_Q = delta_P ≫ target(v) for
  every linear map v. With v=`v.ι.app i` it is precisely the node's actual-cocone
  equation, with Lean's composition order. Applied to transitions it makes
  `projectionTransformation` and its colimit map well-defined. No cocone equation
  is assumed in the hypotheses.
- For every integer q, the next two conjuncts assert invertibility of the canonical
  `colimit.desc` from source and target homology diagrams to homology at B. The
  source desc has legs H^q(v_i tensor 1), giving exactly the leg-induced source
  identification. The target desc has legs H^q G(Lv_i tensor 1), giving the stated
  bounded-below continuity isomorphism. Both act in R_Y-module sheaves.
- The following equality says lambda_q ≫ H^q(delta_B) equals the colimit of
  H^q(delta_{P_i}) followed by rho_q. `colimMap`, whiskering the specified
  `projectionTransformation`, fixes the map on the diagram; it is not merely an
  existence assertion for some compatible homology maps. Inverting lambda_q
  recovers the direction of the identification in the node.
- The final quantified clause covers EVERY representative K, EVERY common lower
  bound n with K^j=0 for j<n, and EVERY isomorphism Q(K)≅C. `strictTensor` is the
  actual signed total of single(LP) with K; there is only one nonzero coefficient
  degree, so its degree j is LP tensor K^j. The clause supplies the representative
  comparison natural in P, an endpoint comparison at B, and the equation on each
  original leg. It asserts the same bound for every stage and B, that this strict
  cocone is a colimit, and that the homology/direct-image colimit comparison for
  this strict diagram is invertible. Thus continuity is explicitly represented by
  the degreewise diagram LP_i tensor K and the original legs, as required.
- Nothing asserts preservation of arbitrary unbounded filtered diagrams or of
  infinite coproducts by G.

Dependency declarations read and used:

- def-pc-flat-sheaf-modules: `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
  `SheafOfModules.IsFlatOnSite`; its body is exactness of `siteSheafTensorRight`.
- def-pc-kflat-complex: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`, together with its existing
  acyclic-tensor interface used by `proEtaleFlatRepresentatives`.
- def-pur-sheaf-tensor-product:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
  `SheafOfModules.cochainModulesMonoidal`, its symmetric/additive instances, and
  `proEtaleOrdinaryTensor`, which is this very sheafified tensor.
- def-weil-abstract-derived-category: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `DerivedCategory.Q`, and `DerivedCategory.singleFunctor`.
- def-weil-pbc-bounded-derived-subcategories is a Mathlib leaf, not a missing
  declaration: `Mathlib.Algebra.Homology.DerivedCategory.TStructure`,
  `DerivedCategory.Plus`, whose object property is `∃ n, C.IsGE n`.
- def-weil-pbc-category-colimit: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `Cocone`, `IsColimit`, `colimit.desc`; filteredness is `CategoryTheory.IsFiltered`.
- def-weil-pbc-proetale-operations: the public-import closure of
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` supplies the arbitrary-ring
  declarations listed in the interface repair below, all read in
  `ProEtaleOperations.lean` and `ProEtaleOperationsCanonicalAdjunction.lean`.
- def-weil-pbc-proetale-site: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology`.
- def-weil-pbc-scheme-conventions explicitly fixes no notion of its own: it is an
  aggregation of existing scheme-morphism definitions. `QuasiCompact` and
  `QuasiSeparated` are the actual Mathlib classes, imported publicly here.
- def-weil-sheaf-of-modules-category: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently Mathlib's `SheafOfModules`.
- def-weil-size-convention is a convention node. The module keeps the original
  site object/Hom sizes, coefficient-sized indices, and the existing large derived
  localization; it does not impose a universe equality to use a specialized API.
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback:
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, its generic
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
  and the already publicly exported `ProEtaleTensorModel`,
  `proEtaleCanonicalTensorPullback` and `proEtaleCanonicalTensorComparison`.
  The full specialization's representative square and unique characterization
  were read; no bare `Nonempty` tensor comparison is used.

The modules of all currently stated proof dependencies are imported with ordinary
`import`, including ProjectionMateExact, ProEtaleBoundedContinuityDirectImage,
KFlatResolutionIndependentCoefficients, the upstream FilteredColimitsTensor,
TensorClosed, ModuleSheavesColimitsForgetful and DegreewiseLimits modules, the
Mathlib finite-additive-coproduct and enough-injectives/derived-plus modules,
RingedToposPullbackFilteredColimits and RingedSiteKInjectiveResolutionsOfUniverses.
`lem-pur-flat-single-derived-normalization` has no recorded declaration, so there
is no proof import for that node yet. It is a proof prerequisite, not an unstated
notion used to type this statement.

Edge cases checked before and during the draft:

- d=0 uses `ULift (Fin 0)` and the empty coproduct; d=1 is the normalized ring case.
- Zero C, zero B and the zero coefficient ring are all admitted. No Nontrivial
  instance is requested; tensoring and cohomology then vanish as expected.
- The empty scheme and empty site covers impose no excluded geometric hypothesis.
- I cannot be empty because filteredness includes nonemptiness. Singleton I is
  included and gives the finite free formula; non-posetal I and noninjective
  transition maps remain admitted.
- C may be unbounded above. Every strict tensor has the single common lower bound
  of the given K; neither a per-stage bound nor an infinite coproduct argument is
  substituted for uniform bounded-below continuity.
- R and S are arbitrary commutative ring sheaves and c is any specified coefficient
  isomorphism. Site object and arrow universes stay different.

Searches actually run in this resumed worker:

1. msearch.py leanfinder: “For a quasi compact quasi separated scheme morphism the
   derived projection formula for a filtered colimit of finite free ring module
   sheaves holds for bounded below complexes”. Eight hits, including
   `Scheme.Modules.instHasColimits`, affine-transition-limit declarations and
   `LightCondensed.free_internallyProjective_iff_tensor_condition'`; no exact match.
2. msearch.py loogle: `"projectionFormula"`. Zero hits.
3. msearch.py grep, Mathlib/CategoryTheory:
   `filtered.*[Ff]inite.*[Ff]ree|projection.*[Ff]ormula`. Zero hits.
4. msearch.py leansearch: “Projection formula for a filtered colimit of finite
   free sheaves and bounded below derived direct image”. Eight hits, chiefly
   sheaf colimit existence, `SheafOfModules.isColimitFreeCofan`,
   `SheafOfModules.Presentation.isColimit`, and filtered sheaf colimits; no exact match.
5. rg in the named live WeilConjectures and Sheaf source directories for
   `filtered.*[Ff]inite.*[Ff]ree|projection.*[Ff]ormula` and
   `filtered.*[Ff]inite.*[Ff]ree|[Ff]inite.*[Ff]ree.*[Pp]rojection`, and for the exact
   node id. No source declaration carries this node or its full filtered-colimit
   statement. Related finite-free, proper, perfect and constant-coefficient
   projection results do not state the arbitrary-ring filtered finite-free
   result with its actual legs and uniformly bounded representatives.
6. Direct source reads found the existing small-site tensor comparison and the
   arbitrary-ring module operations. They are reused through the recorded modules,
   rather than copied. Mathlib's `SheafOfModules.free`, `sigmaComparison`,
   `Limits.Sigma.map`, and the actual derived-category homology functor were read
   and used directly.

Source validation: read the local HRS PDF with pdftotext, Lemma 5.3(1), (5.4)
(lines 983 onward), and the current main-20261015 blueprint's
`det-pe-bounded-continuity-direct-image.md` and its proof. These require one common
lower bound and a qcqs map. Read the unit's `lem-sfb-dc-lower-star-preserves` proof
for the finite-extension/rational coefficient role. The node's finite-free and
cocone assembly is explicitly agent-written from those sources, as its existing
proof_origin records. No source-based correction is necessary and no statement is
disputed.

Validation: the final module has passed scompile.py on the server in module mode,
with explicit variables/universes and no diagnostics. All earlier type errors were
local elaboration errors (finite basis universe, the namespace of Sigma.map, and
Nonempty around the Type-valued IsColimit), corrected without changing the
mathematical statement. Only the prescribed wrappers are used for compilation and
delivery; no live source, tool, library artifact or Git state is edited directly.

## Dependency modules

`def-weil-pbc-proetale-operations`: lean-only Section 1(B) repair, with no new module.
The old recorded declarations named constant-ring specializations, which do not
alone cover this node's arbitrary R_Y. Keep the SAME module, primary declaration,
signature, and constant declarations; additionally list the general
`AlgebraicGeometry.Scheme.proEtaleRingModules`, `proEtaleRingModulePullback`,
`proEtaleRingModuleDirectImage`, `proEtaleRingDerivedPullback`,
`proEtaleRingDerivedDirectImage`, `proEtaleRingDerivedAdjunction`, and
`proEtaleRingDerivedPullbackFactors`. They already belong to the existing module's
public-import closure. Their actual source is ProEtaleOperations and
ProEtaleOperationsCanonicalAdjunction. The latter constructs the canonical derived
adjunction from the unique tensor-unit-normalized module adjunction. This changes
only lean metadata and supplies no new assumption, source definition or object.

`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: lean-only Section 1(B) repair,
with no new module. Preserve the SAME generic independent-universe primary theorem,
signature and recorded module. Additionally list the already public specialization
`AlgebraicGeometry.Scheme.ProEtaleTensorModel`, `proEtaleOrdinaryTensor`,
`proEtaleCanonicalTensorPullback`, and `proEtaleCanonicalTensorComparison`.
RingedTopoiCanonicalTensorPullbackOfUniverses already publicly imports
ProEtaleCanonicalTensorPullback. Its small-site specialization supplies the exact
canonical comparison on the original ProEt site, with the flat-term K-flat
representative square, and no equality of site object and morphism universes.
No old declaration is removed or modified. The actual consumer module compiles
with both repaired dependency imports, providing the consumer validation.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
