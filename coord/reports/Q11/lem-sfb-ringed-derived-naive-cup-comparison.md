## Worker report

The module `Sheaf.CategoryTheory.RingedDerivedNaiveCupComparison` states the complete
Stacks 0FPK equality and its 0FPJ global-sections specialization. Its two theorem
proofs are `sorry`. All definitions have actual data. No statement correction,
new mathematical notion is needed. The returned review requires a definition node
owning an existing data interface; it is recorded with `existing: true`.

Hypotheses and clauses, in order:

- The common small coefficient universe is `u`; `RingedTensorCorner.{u,w}` contains
  `site : Type u`, `Category.{u} site`, its Grothendieck topology, its commutative
  ring sheaf, the ordinary module-sheaf derived category with Hom universe `w`,
  and its tensor functor. There is no equality imposed between `u` and `w`.
  This is precisely the common small-site presentation allowed by the statement.
- The morphism of ringed topoi is `e : RingedTensorEdge Y X`, in the existing
  dependency presentation. Its inverse/direct set-sheaf adjunction is geometric,
  its structural ring map is `e.ringMap`, and its module pullback is the specified
  scalar extension of algebraic inverse image. Its ordinary tensor constraint
  `e.ordinaryTensor` has the generalized pure-tensor normalization, not an
  arbitrary strong monoidal comparison. It imposes no morphism of presented sites.
- `a : RingedTensorModel Y` and `b : RingedTensorModel X` specify precisely the
  flat-term K-flat representative comparisons for the chosen derived tensors.
  These are the same tensor models passed to the recorded cup-product definition.
- `[d : RingedPathRightDerived e]` specifies the right-derived comparison unit
  `d.eta`, its universal right-derived property, and the canonical derived Hom
  normalization with the ordinary module adjunction and the actual left-derived
  comparison. This is the canonical K-flat/K-injective derived adjunction asked
  for by the node, expressed using an existing interface. An unnormalized
  `RingedTensorEdge.derivedAdjunction` alone would not identify beta correctly.
  No boundedness or preservation of K-injectives by direct image is assumed.
- Arbitrary unbounded complexes are `M N : CochainComplex X.mateModules ℤ`.
  Localization `[M]` is `DerivedCategory.Q.obj M`. Termwise direct image is
  `complexDirectImage e`; total tensor is `KFlatFixedTensor.totalTensor` and
  definitionally the recorded signed direct-sum `CochainComplex.mapBifunctor`.
- The canonical arrows rho are `modelTensorAugmentation X b` and
  `modelTensorAugmentation Y a`. Their unique natural normalization includes
  every flat-term K-flat resolution augmentation, not merely some chosen maps.
- Beta is `d.eta.app M`, `d.eta.app N`, or `d.eta.app T` at the total tensor.
  The clockwise composite is `Y.tensor.map (Prod.mkHom betaM betaN)`, then
  the existing `relative e a b`, then `e.right.map rho`.
- The naive chain map `naive e M N` is constructed by the ordinary complex Hom
  bijection: inverse of `e.ordinaryTensor.totalIso`, followed by the total tensor
  of the two componentwise ordinary counits. On a summand this is the section
  tensor pairing followed by direct image of that summand inclusion, by the
  defining ordinary tensor normalization and the adjunction triangles. Both
  total complexes use the same second-differential sign. It uses no assertion
  that direct image commutes with infinite coproducts. This is also the alternative
  definition of naive cup explicitly described in the final paragraph of 0FPK.
- The counterclockwise composite is rho at `(f_*M,f_*N)`, then localization of
  `naive e M N`, then beta at `Tot(M tensor N)`. Lean composes left-to-right,
  hence `derived_naive_cup_comparison` is exactly the displayed node equation.
- The global clause is `global_derived_naive_cup_comparison`, in the actual native
  `DerivedCategory (ModuleCat (scalars X))`, where `scalars X` is the subring of
  compatible ring sections. It uses the recorded `global`, `globalDerivedUnit`,
  and `derivedGlobalSections`. `globalNaive` is the adjunct of
  `mapBifunctorComparison (globalPullbackTensor X)` and the tensor of the ordinary
  counits. The source rho is the native `Functor.LaxMonoidal.μ DerivedCategory.Q`.
  These are module-valued compatible-family global sections; there is no final
  object binder or choice of a final object anywhere in either declaration.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`;
  sites in this theorem are expressed directly by `GrothendieckTopology` as in
  the rest of the recorded arbitrary-ringed-topos API. The size node is a convention.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`;
  its geometric/module datum is represented by the existing tensor-edge interface.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent abbreviation for Mathlib `SheafOfModules`, used by `mateModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `site_derived_tensor_descent_independentCoefficients` and the selected derived
  tensor, through the existing representative-model presentation.
- `Sheaf.CategoryTheory.RingedSiteModuleCupProduct`: `RingedSiteCup.relative`,
  `RingedSiteCup.global`, `RingedSiteCup.globalDerivedUnit`, and its inherited
  global-sections, coefficient-ring and derived-adjunction definitions.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  its total and total maps are used through `KFlatFixedTensor.totalTensor` and
  `HomologicalComplex.mapBifunctorMap`.
- Mathlib `CochainComplex.IsKInjective` (the `mathlib_match` for
  def-pur-kinjective-complex), `Homotopy`, and `QuasiIso` remain the resolution
  notions; no private replacement is introduced.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- `Sheaf.Paper.ProjectionMateExact`: `ringedProjectionMateExact`, its
  `mateModules`, `mateDerived`, `mateTensor`, `mateFlat`, and `mateRepresentative`.
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`:
  `ringedTopoiDerivedPullbackIndependent` (proof import).
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`:
  `module_pullback_pushforward_adjunction` (proof import).
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`:
  `preDerivedAdjunctionGeneral` (proof import).
- `Sheaf.Paper.RingedTopoiTensorComparisonData` and
  `Sheaf.Paper.RingedTopoiTensorComparisonConstruction`:
  `CanonicalRingedTensorComparison`, `canonicalRingedTensorComparison_nonempty`.
- Newly cited landed node def-weil-pbc-ringed-tensor-square-presentation:
  `RingedTensorCorner`, `RingedTensorModel`, `RingedTensorEdge` and
  `RingedTensorEdge.tensorComparison`, in `Sheaf.Paper.RingedTensorSquarePresentation`.
- New definition node def-sfb-ringed-path-right-derived-data:
  `CategoryTheory.RingedPathRightDerived`, in
  `Sheaf.Paper.RingedComparisonTensorAdjunction`.
- Newly cited landed node lem-sfb-ringed-derived-tensor-augmentation-naturality:
  `ringedTensorAugmentation` and `exists_unique_ringedTensorAugmentation`, in
  `Sheaf.Algebra.Homology.RingedDerivedTensorAugmentationNaturality`, retained
  with its original primary declaration and all original declarations retained,
  extended in the same module as described below.
- Newly cited landed node def-sfb-ringed-site-global-derived-adjunction:
  `RingedSiteCup.globalSections`, `RingedSiteCup.globalModuleAdjunction`,
  `RingedSiteCup.globalPullbackTensor` and `RingedSiteCup.derivedGlobalSections`,
  in `Sheaf.CategoryTheory.RingedSiteGlobalDerivedAdjunction`.

The proof-only node lem-sfb-ringed-pullback-derived-ordinary-tensor has no recorded
Lean declaration at this reading, so there is no module to import for it. It is
not needed to type the equality; its exact role is retained in the proof docstring.
Every other recorded proof dependency is imported, publicly when it also supplies
statement data. The extra statement dependencies are the existing tensor presentation and
augmentation nodes, the new existing-definition record, and the existing global
adjunction node. None introduces a dependency path back to this item.

Edge cases checked before writing: identity ringed morphism (the ordinary Hom
bijection reduces naive cup to the ordinary tensor identification); either
complex zero; complexes in negative and positive degrees with unbounded support;
a nonflat structural map such as Z to Z/2 and Z/2 in degree zero. The last case
requires genuinely directed, possibly noninvertible rho and alpha; the statement
retains those maps and adds no flatness assumption. Empty sites/degenerate topoi
are not excluded by any binder. Global sections use compatible families, so sites
without a final object are covered. All variables and universes are explicitly
bound under `set_option autoImplicit false`.

Searches made:

- `msearch.py ... leanfinder "The derived cup product of a morphism of ringed
  topoi agrees with the naive cup product on arbitrary cochain complexes"`:
  eight hits, on HomComplex cocycles, Mayer-Vietoris and sheaf cohomology; no match.
- `msearch.py ... leansearch "Naive cup product on complexes of sheaves and
  comparison with the derived cup product"`: eight hits on total tensor,
  limits and Mayer-Vietoris; no relative derived/naive comparison.
- `msearch.py ... loogle '"mapBifunctorDesc"'`: the constructor and its two
  summand lemmas, supplying the existing coproduct implementation, not this theorem.
- `msearch.py ... grep 'cupProduct|cup_product|naive.*cup|cup.*naive'
  CategoryTheory`: zero Mathlib hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `naive.*cup|cup.*naive`, `naiveCup`, and augmentation names: found
  `ModuleCupNaiveMap` and `ModuleCupNaiveDerivedCompatibility`, which were read;
  those concern scheme/topological global sections with different chosen input
  data, rather than arbitrary geometric morphisms of ringed topoi and this
  recorded relative cup. Also found and reused the new site's augmentation API.
  No exact existing statement was found.

Validation: both delivered Lean files compiled separately through `scompile.py`
on 2026-10-24, in module mode and dependency order, against the published live
server build. No errors or unexpected warnings; final library checks took
16.3 seconds and 22.8 seconds. The required `deliver2.py --no-push` run passed preflight and all server
compiles, printing `OK (dry run)` for commit `16520e7b4cc`; nothing was pushed
by that check. The additional existing-definition probe checked the class and
all three path definitions in their original module.

## New nodes

`def-sfb-ringed-path-right-derived-data` records the existing
`CategoryTheory.RingedPathRightDerived` and the three `ringedPathRightUnit`,
`ringedPathLeftCounit`, and `ringedPathTensorMap` definitions in
`Sheaf.Paper.RingedComparisonTensorAdjunction`. The class includes additivity,
its actual right-derived comparison unit, the universal right-derived property,
and the ordinary/derived Hom normalization. Its source is Stacks 07A6/0FPI;
the path composites use 0D6D/0D6E/07A4. It adds no mathematical construction.
LeanSearch returned eight generic derived-adjunction hits; Loogle for the
class name and Mathlib grep for the class and three composites returned none.
Project rg found the exact existing declarations in that module, which are
reused with `existing: true`; no source was moved or copied. DAG and blueprint
searches found no separate definition node for these data. Raw msearch results
are retained in the node. The theorem node formerly cited for this class has
been removed from the consumer's statement dependencies, as review F1 asks.

## Dependency modules

`lem-sfb-ringed-derived-tensor-augmentation-naturality` retains NI's original
module, primary declaration `SheafOfModules.exists_unique_ringedTensorAugmentation`,
original signature and all original declarations. Its source module
`Sheaf.Algebra.Homology.RingedDerivedTensorAugmentationNaturality` now additionally
publicly imports `Sheaf.Paper.ProjectionMateExact` and appends four declarations:
`modelTensorAugmentationSource`, `modelTensorAugmentationTarget`,
`modelTensorAugmentation_existsUnique`, and `modelTensorAugmentation`
(all in `SheafOfModules`). The original selected independent-coefficient tensor
is not definitionally the corner tensor used by the cup-product API. The
appended declarations give its unique augmentation in that existing tensor-model
presentation, including the inverse representative formula and normalization on
every flat-term K-flat resolution. This is a presentation interface, not a
universe generalization or a replacement of NI's interface. The definition uses
the uniqueness theorem, not a bare existence of an arbitrary map. Its theorem
has the same owning DAG node and the complete proof docstring. No second tensor,
module category, flatness predicate or resolution choice is introduced.
The dependency node changes only in `lean`, with `declarations` a strict superset
and an explanatory note. The old companion module has been removed. The original
module has no live importers, so its added import introduces no cycle.

## Returned review repairs

- F1: added the existing-definition node above and cited it instead of the
  comparison theorem. Existing Lean code and the reviewed cup equalities stay
  unchanged.
- F2: replaced the companion-module rebind with an extension of NI's original
  module and a declaration-list superset. NI's primary declaration and record
  remain intact.
- F3: added `def-sfb-ringed-site-global-derived-adjunction` to `stmt_deps`, since
  its global sections, adjunction, pullback tensor and derived global sections
  are used directly in the global clause.

## Second reading by Q11

Self-check with the node, both modules, and the complete Stacks 0FPK proof open;
the maintainer supplies the independent review specified by this dispatcher brief.
The initial reading identified two interface mismatches and repaired them before
delivery: the augmentation was for the selected tensor rather than the cup's
representative tensor model; and a bare derived adjunction did not carry beta
or its canonical normalization. The augmentation-module extension resolves the first;
the already recorded `RingedPathRightDerived` resolves the second. No mathematical
hypothesis was added to the canonical objects described by the node.

Re-read the source and target of every factor: both sides start at the derived
tensor of localized termwise pushforwards and end at derived pushforward of the
localized ordinary total tensor. Clockwise and counterclockwise orders agree
with 0FPK after reversing written mathematical composition into Lean `≫`.
Re-read the naive map: the inverse ordinary total constraint precedes the tensor
of ordinary counits, then the ordinary complex Hom bijection. No direct-image
coproduct preservation is used. Re-read the global declaration: it uses the
recorded canonical global cup in D(A), not an existential new pairing or
additive-only cohomology. No final object, boundedness, flatness, exact ordinary
pullback, or invertible rho is assumed. No further mismatch found.
