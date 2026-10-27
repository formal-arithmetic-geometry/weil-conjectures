## Worker report

The theorem `AlgebraicGeometry.AlgebraicSpace.affine_relative_cup_sections` states
exactly the three requested compatibility equations. Its proof is `sorry`.
`SpaceAffineCupMaps.lean` supplies canonical scalar/classical-cohomology interfaces
missing from the recorded general ringed-site API. Definitions have actual data;
each comparison chosen by `Classical.choose` is uniquely characterized by its
cycle, chart, or derived-unit normalization. No arbitrary map or tensor structure
is assumed. The four postponed existence-and-uniqueness theorems belong to the
new definition node, whose statement explicitly includes each characterization;
each has a source and a complete natural-language proof in its docstring.

Hypotheses and objects, clause by clause:

- `A B : Type u`, `[CommRing A]`, `[CommRing B]` are the arbitrary commutative
  rings. `Y Y' : Over S`, `e`, and `e'` identify their schemes with Spec A and
  Spec B. An arbitrary `g : Y' ⟶ Y` is equivalent, by the affine anti-equivalence,
  to the node's arbitrary ring map. `spaceAffineRingMap e e' g` is that map,
  formed from the actual morphism on global functions. No ring action is omitted.
- `X X' : AlgebraicSpace S`, `f`, `h`, and `k` are Z, Z', p, h', and p'.
  `sq : IsPullback h.hom k.hom f.hom g'.hom` states precisely their fibre-product
  square in the ambient category of fppf sheaves. This is a pullback of algebraic
  spaces as the recorded full subcategory. `ObjectProperty.hom_ext _ sq.w`
  gives its commutativity; no extra square comparison is a hypothesis.
- `hqc : IsQuasiCompactPresheafMap f.hom.hom` and `hqs` with the diagonal
  are exactly quasi-compactness and quasi-separatedness, as used by the recorded
  affine higher-image sections lemma. There is no affine, proper, flat,
  finite-presentation, Noetherian, or finite-generation hypothesis.
- `M N : X.QCoh` use the recorded full subcategory. The local `F` and `G` are
  their actual restrictions to the small etale model, not replacement coefficients.
  `affineBaseModuleCohomology` and `affineCupH` are the same classical right
  derived section functors. Higher direct images are `smallModuleDirectImage`
  followed by `Functor.rightDerived q`, in all module sheaves.
- Theta is `affineCupEdge`. `CupEdgeSpec` fixes it by the same every-injective-
  resolution formula as `AffineBaseHigherImageSectionsNormalization`. Its second
  conjunct explicitly identifies it on qcqs quasi-coherent inputs with the
  existing chosen isomorphism's forward map. This also handles tensor and
  pullback coefficients, which are quasi-coherent by local presentations. Extending
  the edge to all module sheaves provides a well-typed coefficient interface;
  the theorem itself quantifies only over quasi-coherent inputs.
- Clause (i) is the first conjunct, for all `a b : ℕ`, `x`, and `y`. Its left
  side is theta on `affineGlobalCup`; its right side is
  `affineSectionTensor` of the two theta images followed by section functor
  applied to `spaceModuleCup`. `affineSectionTensor` sends the pure tensor of
  two sections to their sheaf tensor using the inverse left unitor. Thus its
  evaluation at `x,y` is precisely the value of the A-balanced tensor map in
  the node. `affineGlobalCup` uses the recorded `globalModuleCup`, after exact
  restriction from Γ(Z,O_Z) to A and the canonical classical/unbounded comparison.
- Clause (ii) is the second conjunct, an equality of A-linear module morphisms
  for every `M,q`. `affineCupCohomologyPullback` is the canonical derived
  pullback unit and actual sections compositor, followed by the augmentation to
  ordinary pullback coefficients, transported to classical right-derived objects.
  The other route is theta, `affineCupSectionPullback` on the affine base, then
  sections of `cupModuleBaseChange`. The target A-module is explicitly
  `ModuleCat.restrictScalars (spaceAffineRingMap e e' g)` of the B-module.
- Clause (iii) is the third conjunct, an equality of sheaf morphisms. The left
  route is ordinary base pullback of relative cup followed by beta for F tensor G.
  The right route is the existing normalized ordinary tensor comparison on the
  base, tensor of the two beta maps, relative cup for k, then higher direct image
  of the inverse coefficient tensor comparison for h. Consequently both routes
  have identical source and target. Equality of these sheaf morphisms is exactly
  equality on every local section, including the pure tensors u tensor v of the
  node. Local pure tensors generate the sheaf tensor. No assertion that beta is
  invertible, or that ordinary pullback is exact, occurs.

Dependency declarations used:

- Mathlib's `AlgebraicGeometry.Scheme`, `CategoryTheory.Over`, `IsPullback`,
  `ModuleCat.restrictScalars`, `Functor.rightDerived`, `InjectiveResolution`,
  `Functor.homologyRightDerivedFunctorObjSingleFunctorIso`,
  `Functor.mapDerivedCategoryHomologyFunctorIso`, and `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `schemeSpace`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the module-sheaf category used by the existing small models.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`,
  `moduleTensorPullback`, `moduleTensorAdjunction`, `moduleDirectImageModel`,
  `moduleChartScalar` and their small-model transports.
- `Sheaf.CategoryTheory.RingedSiteModuleCupProduct`:
  `RingedSiteCup.globalModuleCup`, `cohomologyPairing`, `tensorAugmentation`,
  `globalSections`. The specialized relative cup uses the exact defining formula
  of `RingedSiteCup.relative`: transpose the tensor comparison followed by the
  tensor of counits. Its coefficient product uses exactly the existing pairing
  and augmentation. The general relative definition takes a `RingedTensorEdge`
  with a literal geometric inverse-image presentation. The recorded algebraic-
  space interface supplies its transported module adjunction and tensor comparison
  instead, so the specialization uses those existing data directly. It does not
  introduce another cup convention or tensor model.
- `Sheaf.AlgebraicGeometry.SpaceAffineBaseHigherImageSections`:
  `exists_affineBaseHigherImageSections_iso`, `affineBaseModuleCohomology`,
  `affineBaseHigherImageSections`, and the resolution-complex abbreviations.
- `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`: `affineScalarSections`,
  `affineGlobalScalar`, `affineDerivedSections`.
- `Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors`:
  `affineSectionsComposition`, `fullModuleSection`, `affineSectionsComplexUnit`.
- `Sheaf.AlgebraicGeometry.SpaceAffineHomComparison`: `spaceAffineRingMap`,
  `spaceSmallTensorAdjunction`, `spaceDerivedAdjunction`,
  `spaceRightDerivedComplexUnit`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`: `spaceDerivedPullbackComp`,
  `spaceDerivedPullbackCounit` and the small/derived module functors.
- `Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations`:
  `moduleDerivedPullbackTensor` and its fixed tensor-model comparisons.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePullbackTensorComparison`:
  `SingleComplex.ordinaryTensor`, with its local pure-tensor normalization.

Edge cases checked before finalizing: a=b=q=0 gives ordinary section/tensor
identities and the underived base-change mate; M=0 or N=0 gives zero products;
the zero ring and empty affine base are allowed (no Nontrivial instance); identity
base change recovers ordinary functor comparisons. The nonflat map Z→Z/n is
allowed: beta is an ordinary comparison, not an isomorphism, and the augmentation
from derived to ordinary coefficient pullback is retained. A qcqs nonaffine Z,
with Γ(Z,O_Z) larger than A, uses scalar restriction rather than identifying the
two rings. Small modules, rings and schemes retain universe u; the canonical
native localizations are used, without equating separately bound universe levels
or imposing any additional instance hypothesis.

Searches: msearch LeanFinder "affine base global sections relative cup product
compatibility arbitrary base change algebraic spaces" returned eight unrelated
scheme affine-space morphism lemmas. Loogle "SheafOfModules,
CategoryTheory.Functor.rightDerived" returned no hits. Mathlib grep
"cupProduct|cup_product|AlgebraicSpace" returned no hits. LeanSearch "cohomology
tensor pullback cup product algebraic spaces affine global sections" returned
scheme global-section results, not this statement. The new node also records the
fresh LeanSearch query "canonical comparison affine scalar global sections module
cohomology pullback cup product" (eight ordinary scheme/presheaf declarations)
and LeanFinder "canonical scalar cocycle pullback cohomology base change cup
product sheaf modules" (eight group-cohomology cocycle declarations). Repository
rg searches in WeilConjectures and Sheaf located the already recorded tensor,
section, adjunction and cup constructions above; these are reused. Searching
DAG and both source trees for `cupCorner|affineCup|cupModuleBaseChange|SpaceAffineCupMaps`
found no prior interface. Searches for section/cup and scalar/cocycle terminology
in DAG nodes found the generic ringed hypercohomology edge nodes and existing
affine sections nodes, not this specialization. `tools/blueprint_refs.py ancestor`
returned the item's null ancestor; the new node retains its via chain.

Both delivered files compiled cleanly through scompile.py in dependency order:
SpaceAffineCupMaps 24.5/25.1 seconds, SpaceAffineRelativeCupSections 6.8/7.7
seconds (sandbox/library). No diagnostic commands remain. There is no statement
correction or disputed mathematical statement.

## Second reading by Q18

This is a separate self-reading with the node and both files open. The dispatcher's
explicit instruction forbids starting other agents, so I do not claim an
independent worker review; the maintainer's independent delivery review remains.

I checked each binder against the node: arbitrary rings and affine models, the
actual ring map, the fibre-product square, qc and qc diagonal, QCoh coefficients,
nonnegative degrees and arbitrary classes. I checked the three equations in
order, including the restriction of B-scalars in (ii) and the inverse coefficient
tensor comparison at the end of (iii). An earlier scratch statement only exposed
derived formulas and did not state the three requested cohomological conclusions;
it was replaced completely before delivery. I also checked that the ordinary
scalar/cocycle comparison in beta is not inverted and that global pullback retains
the coefficient augmentation. No extra flatness or cohomological vanishing
hypothesis was added. The new node's normalization predicates specify the unique
maps used by its definitions; its four postponed theorems each match a uniqueness
assertion in its statement, not the compatibility conclusions of the main item.

## New nodes

`def-sfb-space-affine-cup-maps` owns SpaceAffineCupMaps.lean. It gives the
canonical scalar/classical-cohomology comparisons, normalized edge, specialized
relative and global cups, scalar/cocycle pullback, counit-mate exchange and ordinary
beta, and actual affine-scalar section/cohomology pullback. Sources are Stacks
0B6C, 0FPJ, 03FD, 07A7, 0BKV, 0D6H, 0FPN, 0H9A, with 08EX identifying the
edge on quasi-coherent coefficients. Searches and reused dependencies are listed
above and in its mathlib_searches. Existing general cups, affine section functors,
and derived adjunctions do not provide these combined classical-cohomology
interfaces. Their underlying constructions are reused, rather than replaced by
arbitrary morphisms. All uniqueness properties used to choose maps are explicit
parts of this node, with actual chart/cycle/derived-unit equations in Lean.

## Saved-packet self-check by Q18

The saved packet passed the current server preflight and both per-file compiles.
I reread the item and both modules. The three conjuncts retain the global/relative
cup equation, scalar-restricted cohomology pullback equation, and sheaf-level
base-change cup equation. I expanded the theorem statement’s local `let` aliases
for the restricted coefficients and base morphism, as required by the current
no-let statement convention. This changes no mathematical hypothesis or clause.
The node’s recorded signature is updated verbatim.
