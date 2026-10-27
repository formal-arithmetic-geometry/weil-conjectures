## Worker report

The module `Sheaf.CategoryTheory.SystemSingletonGeometricPullback` states
`SheafOfModules.systemSingletonGeometricPullback`. Its proof is `sorry`; every
helper definition has real data. Its conclusion includes an exact termwise inverse
image and a `SystemSingletonGeometricComparisons` existential proposition, with the actual derived
natural isomorphisms and their normalizations. Nothing is restricted to bounded
complexes or flat coefficient maps. No statement correction or dependency repair
is needed, and no statement is disputed.

Source read: Zheng, Construction 4.1, printed p. 21, and the sentence immediately
before Lemma 4.10, printed p. 23 (the PDF is in literature). Construction 4.1 gives
the scalar-tensor/zero singleton extension; the later sentence gives its derived
base-change isomorphism, in the inverse direction to the one in this node. The
node's supplied six-step proof expands the tensor-generator and lower-singleton
normalizations. The theorem docstring records all six steps and how to descend
whole-system cochain equalities, without claiming that derived evaluation detects
equality of morphisms.

Hypothesis and clause correspondence:

- The sites have independent object and morphism universes `uC`, `vC`, `uD`,
  `vD`. Their module universe is `w`. `EssentiallySmall.{w}` states the required
  size bound. `HasSheafify`, `WEqualsLocallyBijective`, and `HasSheafCompose`
  expose the canonical sheafification/abelian APIs valid under that bound.
- `u : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))` is an arbitrary
  geometric morphism: the existing structure supplies inverse/direct image,
  their adjunction, and left exactness. No underlying site functor is required.
- `BY`, `BX : ℕᵒᵖ ⥤ Sheaf ... CommRingCat.{w}` are the two actual ring towers.
  `I n : AlgebraicInverseImage u.inverse ...` identifies each target ring with
  the inverse-image ring and specifies the induced module inverse image.
  `htransition` is the commuting square transporting the source ring transitions;
  it states precisely the node's 'including the pulled-back transitions'.
- A natural index `n` represents positive level `n+1`, following the recorded
  strict-system library. This includes the first level with no missing case.
- Modules are exactly `systemLevel BY n`, a transparent specialization of
  `CategoryTheory.ringedSiteModules` and hence Mathlib `SheafOfModules`.
  Strict systems, linear maps, and transitions are the existing `StrictRingSystem`;
  no new system category or derived category is introduced.
- `SY`, `SX : SystemScalarAssignment` and `TY`, `TX : SystemTensorCoherence` select
  the dependency's universally normalized scalar models and their tensor coherence.
  The theorem is for every such choice. They impose no extra coefficient property.
- `SystemGeometricInverseImageData.functor` is `G_B`. Its evaluation isomorphisms
  identify its levels with `(I n).modules`, while its `transition` field fixes the
  underlying semilinear transition using `u.inverse.map` and the existing
  `moduleUnderlying` identifications. Thus this is termwise inverse image on actual
  systems, including morphisms (naturality of evaluation). Its functor and level
  exactness fields are conclusions, not assumptions added to the theorem.
- `SystemGeometricInverseImageData.levelFunctor` is transparently `(I n).modules`;
  this wrapper retains the exactness witness for instance inference. Its derived
  functor is the existing exact `Functor.mapDerivedCategory`. `derivedEvaluation`
  is explicitly constructed from the existing exact-functor compositors and
  `mapDerivedCategoryNatIso`, not postulated as an arbitrary square.
- The singleton extension and evaluation are the recorded
  `systemSingleDerivedExtension ...` and `derivedSystemEvaluation ...`.
  The existential `comparison` family is the requested whole-system natural isomorphism
  `(systemSingleDerivedExtension BY n ...).derived ⋙ F.functor.mapDerivedCategory ≅
  (F.levelFunctor n).mapDerivedCategory ⋙
  (systemSingleDerivedExtension BX n ...).derived`.
- The ordinary representatives are the `ordinary` natural isomorphisms of functors
  into `StrictRingSystem BX`, not unrelated evaluated isomorphisms. Their components
  are therefore strict system maps, whose `Hom.comm` is exactly compatibility with
  every actual transition. Naturality in the module makes their termwise maps into
  cochain maps for all complexes, via `NatIso.mapHomologicalComplex`.
- Below `n`, `tensor` compares the actual scalar model functors.
  The conjunct labelled `tensor_evaluation` identifies evaluation of the ordinary system comparison with
  those tensor maps, using `systemSingleBelow` from the dependency.
  The conjunct labelled `tensor_generators` fixes the canonical map on every generalized pure tensor:
  `systemModelTmul` on the source is transported through `moduleUnderlying`, and
  its image is `systemModelTmul` of the transported scalar and vector on the target.
  Testing every sheaf `Z` includes universal local sections, not only global ones.
- Above `n`, The conjunct labelled `above` gives the unique zero morphism. The dependency's
  `systemSingleLevelAbove` identifies both objects with zero, where this unique
  morphism is also the identity of zero. Thus this does not assert a zero map
  between possibly nonzero components.
- The conjunct labelled `flat_models` assumes precisely `systemLevelKFlat BY n Q`: independent K-flatness
  and flat terms. It concludes the same property for the inverse-image complex
  and concludes K-flatness plus flat terms on the actual ringed sequence sites for
  both ordinary singleton complexes. Reassembly uses the existing
  `strictSystemToSequenceFunctor` and `systemSequenceRing`; no surrogate predicate
  replaces sequence-site K-flatness.
- The conjunct labelled `representative` is the equality in the derived category expressing `c_n` on
  the same `Q`: the two recorded normalized derived comparisons and the exact
  inverse-image factorization identify its value with `Q.map` of `ordinary`.
  `flat_models` and the dependency's `computes` ensure these comparison arrows
  are invertible on that class.
- `systemSingletonOrdinaryMultiplication` is explicitly `systemSingleBelow` followed
  by `TY.ordinaryUnit`. The conjunct labelled `multiplication` expresses the level-n identity
  after these multiplication maps. `systemSingletonDerivedMultiplication` is the
  recorded `systemSingleDerivedBelow` followed by `TY.derivedUnit`, and
  `derived_multiplication` expresses the same normalization on every derived input.
- `systemSingletonLowerMap` is the actual singleton-adjunction transpose of the
  inverse below-level evaluation comparison. By the dependency's normalized
  transpose formula, its below-n components are the canonical tensor associators
  and its above-n components have zero source. No arbitrary lower arrow is bound.
- `scalar` gives the derived scalar/pullback comparison, and
  `scalar_representative` fixes it to the same canonical ordinary tensor comparison
  on flat-term K-flat representatives. `lower_singleton` is the full derived square
  intertwining `c_n`, `c_m`, these scalar comparisons, and the actual lower arrows
  for every `h : n ≤ m` and every derived `P`.

Dependency declarations read and used (their full definitions, signatures and
source docstrings were opened):

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, reexporting the general site API.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; standard unbounded localization.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite` and `CategoryTheory.exactFunctor`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`; used through `systemRestriction`.
- `Sheaf.CategoryTheory.SystemRingedSequenceSite`:
  `strictSystemSequenceEquivalence`, `strictSystemToSequenceFunctor`,
  `systemSequenceRing` and `systemSequenceModules`.
- `Sheaf.CategoryTheory.SystemLevelLeftExtension` and its public basic interface:
  `systemLevelLeftExtensionTheory`, `StrictRingSystem`, `systemLevel`,
  `systemEvaluation`, `derivedSystemEvaluation`, `SystemScalarAssignment`,
  `SystemTensorCoherence`, `systemLevelKFlat`, `systemTensor`, `systemDerivedTensor`.
- `Sheaf.CategoryTheory.SystemSingleDerivedExtension`:
  `systemSingleDerivedExtension`, the normalized derived ordinary singleton extension.
- `Sheaf.CategoryTheory.SystemOrdinarySingleExtension`:
  `systemSingleFunctor`, `systemSingleBelow`, `systemSingleLevelAbove`,
  `systemSingleAdjunction`, `systemSingleTranspose`.
- `Sheaf.CategoryTheory.SystemSingleDerivedEvaluation`:
  `systemSingleDerivedBelow` and `systemSingleDerivedTranspose`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel`, through the scalar models' `model.E`,
  `model.T`, `model.ε` and their fixed tensor generators `systemModelTmul`.
- `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism` was read; its restriction to small sites
  with equal site universes is unnecessary here. The geometric adjunction and
  algebraic inverse-image structures already publicly reexported by the recorded
  dependencies express this node's unringed geometric morphism and inverse-image
  coefficients without that restriction or an arbitrary structural ring map.
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses` publicly reexports
  `Sheaf.CategoryTheory.AlgebraicInverseImage`:
  `SheafOfModules.AlgebraicInverseImage`. This existing specialization has the
  same module/coefficient universe `w` required for these towers, while retaining
  independent site object and morphism universes. No second inverse-image notion
  is constructed. The generalized recorded interface was also read.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal`; `Mathlib.Algebra.Homology.BifunctorShift`:
  `CochainComplex.mapBifunctor`, used in the imported K-flat definition.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`:
  `CategoryTheory.GeometricMorphism` (existing node `def-trf-geometric-morphism`).
- `Sheaf.CategoryTheory.SystemEvaluationTopos`:
  `strictSystemToSequenceAdditive`; this public instance is needed to form the
  sequence-site singleton complexes using reassembly.

The three existing landed nodes `def-trf-geometric-morphism`,
`def-weil-pbc-algebraic-inverse-image`, and `lem-pur-system-evaluation-topos` are
added to `stmt_deps` to expose these actual interfaces, as authorized by the
standing brief's rule for adding landed statement dependencies. Their nodes and
modules are not changed. All stated proof-dependency modules are imported, with
proof-only imports private. Small wrappers, normalizations, and the two conclusion
packages belong to this owning node, are listed in `lean.declarations`, and all
have source and blueprint docstrings. No new independent notion or DAG node is
introduced.

Edge cases checked before writing and again against the signature: first index
`n=0` (paper level 1); `j>n`, including the boundary transition with zero source;
`m=n` (identity coefficient map and tensor unit); arbitrary nonflat transitions,
for example the punctual topos tower with Z/4 to Z/2; zero rings and zero modules;
empty sites; unbounded complexes; and independently sized sites. None is excluded
by the signature. All isomorphisms are in the actual derived category of strict
systems, not a diagram category formed from level derived categories.

Searches for an existing declaration:

- `msearch.py ... leanfinder "Derived singleton extension of sheaves of modules
  over an inverse ring system commutes with geometric inverse image"`: eight
  ordinary free-module/pullback and pushforward comparison hits, including
  `SheafOfModules.freeFunctorCompPullbackIso` and `ιFree_mapFree_inv`; none gives
  strict-system derived singleton base change or its normalizations.
- `msearch.py ... loogle "CategoryTheory.evaluation, CategoryTheory.Adjunction"`:
  five hits, including `evaluationAdjunctionLeft`, `evaluationAdjunctionRight`,
  `constantPresheafAdj` and the simplicial chain-complex adjunctions. These concern
  fixed-category functor evaluation, not varying sheaf-ring coefficient systems.
- `msearch.py ... grep "single.*(pullback|inverse)|singleton.*derived"
  CategoryTheory`: twelve hits in matrices, singleton sieves and wide pullbacks;
  none matches.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for geometric/system,
  singleton/pullback and inverse-image names found the existing system evaluation,
  scalar, ordinary singleton, and derived singleton interfaces inspected here;
  generic scheme single-complex comparisons concern a different construction.
  Exact item-id search in `lean/WeilConjectures` found no declaration.
- Exact new-name search in both source roots and `dag/lean_names_upstream.json`
  found no preexisting `systemSingletonGeometricPullback`,
  `SystemSingletonGeometricComparisons`, or `SystemGeometricInverseImageData`.

## Second reading by NA

Internal rereading of the actual node and module: the hypothesis/field mapping
above was checked against every paragraph of the node, rather than merely checking
that an isomorphism exists. The main checks were that inverse-image ring transitions
are explicit, the representative is a whole strict system map, multiplication uses
the dependency's actual units, and the lower arrow is the normalized adjunction
transpose. The lower-square direction is source-to-target on both paths. The
zero-component clause is equivalent to identity of zero because the dependency
proves the singleton vanishes there. No hypothesis or clause mismatch was found.
The first compiler checks required exposing the reassembly additivity instance and
retaining level exactness witnesses in the `levelFunctor` wrapper; these adjustments
change no mathematical object. No other agent was started, as the dispatcher
explicitly prohibited that; the maintainer performs the independent review.

Compilation diagnosis: profiling identified automatically generated constructor
injectivity, recursion and size-of lemmas for the large comparison data structure
as unnecessary kernel work. Its final representation is an existential proposition
with the same four families and nine labelled conjuncts, avoiding those unused
generated lemmas. The remaining inverse-image data structure locally disables
`genInjectivity` and `genSizeOfSpec`. The mathematical statement is unchanged.
The diagnostic profiler option was removed and the 60-second limit was never raised.
Both the sandbox and library-module compiles passed cleanly in approximately 20 seconds.
