## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.exists_affineFormalFunctions` in
`Sheaf.AlgebraicGeometry.SpaceAffineFormalFunctions`. Its only theorem has proof `sorry`.
The module also constructs the actual infinitesimal spaces, their maps, the tensor
coefficient arrows, a resolution-normalization predicate, and the compatible-sequence
limit. These are helpers for the maps in this node, all listed in `lean.declarations`;
there is no new independent definition node, dependency repair, or statement correction.
All definition data are real expressions; none is selected from a mere existence claim.

I read the node, all eleven original statement-dependency nodes and their recorded
interfaces, the current compact-object example and its upstream replacement, and the
stage instructions. I checked Stacks spaces-cohomology.tex, Situation
`situation-formal-functions`, Theorem `theorem-formal-functions` (08AZ), and the final
paragraph of `lemma-formal-functions-stalk` (08B1). The latest blueprint unit
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` is unchanged by this work.

Hypothesis and clause correspondence:

- A Noetherian commutative ring: `A : Type u`, `[CommRing A]`, and
  `[IsNoetherianRing A]`. There is no `Nontrivial` assumption.
- An arbitrary ideal: `I : Ideal A`; neither maximality nor ideal-adic completeness is
  assumed.
- A proper morphism of algebraic spaces to Spec A: `{S : Scheme.{u}}`,
  `Y : Over S`, `a : Y.left ≅ Spec (.of A)`, `{X : AlgebraicSpace S}`,
  `f : X ⟶ schemeSpace Y`, and `hf : MapIsProper f`. The extra names S,Y,a only
  represent the base scheme and its affine identification. They do not restrict it:
  the original case takes S=Spec A, Y=Over.mk (𝟙 S), a=Iso.refl S; conversely any
  supplied Y,a gives precisely the source situation over an affine scheme.
- Coherent F: the family `d` ranges over `F : X.Modules`, `F.IsQuasicoherent`,
  and `∀ T : X.EtaleSite, RingedSpace.IsCoherent ... ((X.schemeRestriction T).obj F)`.
  This is equivalent to the node's affine-cover description. Proper finite type over
  the Noetherian affine base makes every chart locally Noetherian. On a Noetherian
  affine, coherent quasi-coherent sheaves are exactly associated finite modules.
  Conversely, finite generation on the given affine etale cover descends to each
  affine chart using a finite affine refinement and faithfully flat finite-module
  descent, exactly as step 1 of the accepted DAG proof explains. Zariski locality
  extends from affine charts to every etale chart. Thus no hypothesis is strengthened.
- Small etale module sheaves and tensor pullback: `X.Modules`,
  `moduleTensorPullback`, and `moduleTensorAdjunction` are the recorded definitions;
  their chart-limit and scalar-one-unit normalizations are retained.
- Cohomology by injective resolutions in ALL module sheaves: `affineFormalH` is
  `X.smallModuleRestriction ⋙ (affineScalarSections ...).rightDerived q`.
  Restriction is the recorded equivalence with the small ringed model, preserving the
  original section universe. Only the theorem's inputs are coherent; derivation is
  never performed in QCoh or the coherent subcategory. Enough injectives comes from
  the existing Grothendieck module category theorem, with no extra hypothesis.
- Every q>=0: `q : ℕ`, including q=0.
- Every positive n: the Lean index `n : ℕ` means the mathematical exponent n+1.
  `affineFormalBase` is Spec(A/I^(n+1)), with the actual quotient scheme map;
  `affineFormalSpace` is its sheaf fibre product with X; `affineFormalι` is the
  first projection. `affineFormalModule` is exactly j-star F.
- The restrictions are the canonical maps: `restriction_normalized` uses the
  adjunction unit F -> j_*j-star F as coefficient arrow. The predicate
  `AffineFormalRestrictionNormalized` specifies a roof on every pair of injective
  resolutions and every intermediate injective resolution of j_*F_n. Its termwise
  map is given by `affineFormalPushSection`, using the recorded
  `moduleStructureMap`, `smallModuleUnitIso` and `fullModuleSection`. The comparison
  is required to be invertible in degree q. The homology equation fixes the
  restriction, rather than admitting an arbitrary linear map.
- No unsupported preservation of injectives is used: the intermediate resolution K
  is a resolution of j_*F_n. The map t goes FROM j_* of the chosen fibre resolution
  INTO K; the map v goes from the source resolution into K. The section comparison
  w is normalized termwise. These are the usual resolution roofs. This avoids the
  generally invalid assertion that the tensor right adjoint preserves injectives.
- Annihilation: `kills n` is I^(n+1) H <= ker(restriction n).
- The induced quotient maps: `theta n` has domain H / I^(n+1) H, and
  `theta_projection` identifies its composite with `Submodule.mkQ` with the
  prescribed restriction. Hence it is the unique induced map.
- Compatibility: `theta_transition` uses Mathlib's
  `AdicCompletion.transitionMap` at `Nat.succ_le_succ h` for every n<=m.
  `transition_id` and `transition_comp` give the inverse system laws.
- The right transitions are geometric restrictions: `affineFormalBaseTransition`
  is Spec of the quotient factor A/I^(m+1) -> A/I^(n+1);
  `affineFormalTransition` is its actual pullback map. The coefficient arrow
  `affineFormalCoefficient` is the tensor-adjunction unit followed by direct image
  of `affineFormalTensorTransition`. The latter is the existing tensor-normalized
  associativity comparison, transported by the pullback-projection equality.
  `transition_normalized` imposes the same resolution roof for this exact arrow.
- Completion of H: the source of `comparison` is Mathlib `AdicCompletion I H`,
  whose definition is the compatible sequences H / I^k H. Its k=0 coordinate is
  necessarily zero; using the positive levels k=n+1 is the canonical cofinal
  identification, not a dropped level.
- The right inverse limit: `affineFormalLimit` is the actual submodule of the
  product of the H^q(X_(n+1),F_(n+1)) whose coordinates satisfy every transition.
  No unrelated limit object or isomorphism is substituted.
- The inverse limit of theta: `comparison_projection` says that the nth coordinate
  is theta_n applied to `AdicCompletion.eval ... (n+1)`. This fixes the comparison.
- Isomorphism of completed-ring modules: `comparison` is a
  `≃ₗ[AdicCompletion I A]`. Its source has Mathlib's actual completion action.
  The target `limitModule` is fixed by `coordinate_action`: for every completed
  scalar c and sequence x, its nth coordinate is b times x_n whenever b represents
  `AdicCompletion.evalₐ I (n+1) c`. Every residue class has such a representative;
  the clause therefore fixes the action on every coordinate uniquely, including
  independence of representatives. This is precisely the stated coordinate action.
  It also forces agreement with the limit's original A-action by taking c=of(b).
- Naturality: the final universally quantified equation in the theorem commutes the
  comparisons with `AdicCompletion.map I ((affineFormalH ...).map g).hom` and
  `(affineFormalHn ...).map g` for every map g between coherent modules and every
  completion element and positive coordinate. Equality of all coordinates is
  equality in the inverse limit. The maps on the fibres use the already defined
  tensor pullback functor; no arbitrary lifts or natural transformations appear.
- No completeness, locality or flatness assumptions occur anywhere in the signature.

Dependency declarations used (module -> names; all under AlgebraicGeometry.AlgebraicSpace
unless another namespace is shown):

- Mathlib.AlgebraicGeometry.Scheme -> AlgebraicGeometry.Scheme, Spec, Spec.map;
  Mathlib.RingTheory.Noetherian.Defs -> IsNoetherianRing;
  Mathlib.RingTheory.Finiteness.Defs -> Module.Finite, underlying the local description.
- Sheaf.AlgebraicGeometry.AlgebraicSpace -> AlgebraicSpace, EtaleSite,
  structureSheaf, Modules.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule -> the specialization of
  Mathlib SheafOfModules.IsQuasicoherent; no replacement predicate.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations -> moduleDirectImage,
  moduleTensorPullback, moduleTensorAdjunction.
- Mathlib.CategoryTheory.Preadditive.Injective.Basic and .Resolution ->
  CategoryTheory.Injective, InjectiveResolution; Mathlib.CategoryTheory.Abelian.RightDerived
  -> Functor.rightDerived, InjectiveResolution.isoRightDerivedObj.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers ->
  fibreProduct_isAlgebraicSpace; Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite ->
  schemeSpace, enlargedFibreProduct, enlargedFibreProductFst.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality -> MapIsProper,
  reexported from AlgebraicSpaceMorphismProperties and used without a private copy.
- Mathlib.RingTheory.AdicCompletion.Basic, .Algebra and .Functoriality ->
  AdicCompletion, transitionMap, eval, evalₐ, its completed-ring Module instance, map.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel -> smallModuleRestriction,
  smallModuleEquivalence, SmallModules, smallStructureRings;
  .AlgebraicSpaceDerivedModules -> smallModuleDirectImage and its Additive instance.
- Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections -> affineScalarSections;
  .SpaceAffineSectionsCompositors -> smallModuleUnitIso, fullModuleSection.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap -> moduleStructureMap;
  .SpaceFlatDirectImageBaseChange -> moduleTensorComposition, whose local tensor
  formula is normalized by its existing unique-existence theorem.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction -> schemeRestriction;
  .CoherentFiniteType publicly exposes the recorded
  AlgebraicGeometry.RingedSpace.IsCoherent from WeilConjectures.AlgebraicGeometry.Coherent.

The eight additional stmt_deps are these already landed owning nodes for small-model,
scalar-section, structure-map, tensor-composition and chart-coherence interfaces. Each
has a usable Lean record; a dependency traversal found no path back to this item.
No original stmt_dep was removed or modified.

Available proof dependencies are imported as ordinary imports, including coherent
abelian closure, affine higher-image vanishing, affine-base sections comparison,
module/abelian evaluation comparison, the universal delta functor, scheme Zariski/etale
comparison, Noetherian finite-type permanence, Artin-Rees and faithful-flat finite-module
descent. The proof docstring follows all twelve accepted DAG steps. Proof-only nodes
without recorded declarations are not restated. The recorded
`Sheaf.CategoryTheory.RingedSiteCohomologyFmapCalculus` source was absent locally;
`scompile.py --source` returned "Module source unavailable". The delivered roof
predicate states the maps needed here directly using the available canonical units and
structure maps; it introduces no copy of that general calculus and no dependency wait.

Edge cases checked before writing and again after compilation:

- q=0 remains the right-derived degree-zero sections functor, with ordinary unit
  restriction and the same resolution normalization; no positive-degree hypothesis.
- I=0 gives X_n=X and the usual completion H=H; no separatedness of the I-adic
  topology is assumed on H.
- I=A gives empty infinitesimal spaces, zero positive quotient modules and zero
  completion/limit. The zero ring is permitted; no nonempty affine base is assumed.
- F=0 and X empty give zero modules with the displayed maps and unique actions.
- Arbitrary ideals and nonflat coherent F are included; no flatness is hidden in a
  pullback exactness assumption. Resolution roofs use direct image, not tensoring an
  injective resolution.
- All field characteristics and arbitrary scheme universe u are retained. The index
  set is exactly the natural-number positive tower, not an independent size restriction.

Searches performed (all msearch queries were actually run):

- leanfinder: "Formal functions for proper algebraic spaces over a Noetherian affine
  base: completion of coherent cohomology is the inverse limit of infinitesimal fibre
  cohomology". Eight hits: scheme affine-transition-limit sections results and BDeRhamPlus;
  no algebraic-space formal-functions statement.
- loogle: `"AdicCompletion", "cohomology"`. Zero hits.
- grep: `formal.functions|formalFunctions|AlgebraicSpace`. Three Mathlib hits in monoid
  algebra pointwise scalar multiplication and complex conformal maps; none relevant.
- leansearch: "For proper algebraic spaces coherent cohomology completed at an ideal
  equals the limit of the cohomology on infinitesimal thickenings"; additionally
  "Formal functions for coherent sheaves on proper algebraic spaces". Returned generic
  scheme/module and quasi-coherent data APIs; no matching theorem.
- rg of lean/WeilConjectures and lean/Sheaf for formal-functions/cohomology/completion
  names found the existing SCHEME theorem in
  WeilConjectures.AlgebraicGeometry.TheoremFormalFunctions and its specialized consumers,
  and algebraic completion infrastructure. They do not quantify over algebraic spaces.
- grep of the item id in lean/WeilConjectures returned no match. Searches for the new
  affineFormal names found only the unrelated preexisting affineFormalIdeal.

Validation: `scompile.py NX lem-sfb-space-affine-formal-functions <module>` compiles the
sandbox module and the intended library module separately under the standard 60-second
per-file limit. The final delivered version is checked again by deliver2.py.
There are no statement disputes or known node faults.

## Second reading by NX

This is an in-thread worker self-check; no second agent was started, as the dispatcher
brief explicitly prohibits delegation. The maintainer's independent delivery review
remains required. I reopened the node and compared every hypothesis and clause with the
final file. The detailed correspondence is above. In particular I checked the chartwise
coherence equivalence against accepted proof step 1; the positive-level reindexing;
the actual quotient-ring fibre-product maps; the unit followed by tensor-associativity
coefficient map; all-resolution normalization of both kinds of restriction; quotient
factorization and compatibility; the coordinate projection fixing the completion map;
the actual completed-ring linear equivalence with its fixed coordinate action; and the
final naturality equation. The intermediate roof map is explicitly required to induce
an isomorphism, preventing a vacuous or noncanonical normalization. The revised
comparison uses the completed ring as its scalar ring, not merely an A-linear
isomorphism. No hypothesis, conclusion, tower, or scalar action was replaced. No change
to the informal statement was needed.
