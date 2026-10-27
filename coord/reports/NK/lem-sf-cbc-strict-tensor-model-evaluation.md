## Worker report

Item: lem-sf-cbc-strict-tensor-model-evaluation. The delivery states the
strict tensor-model and exact-evaluation computation. Two definition modules supply
the ordinary and derived computation interfaces, and the item module supplies the
theorem and the two exact slice-extension composites. Its only postponed proof
is the named theorem `SheafOfModules.StrictTensorEvaluation.strict_tensor_model_evaluation`.
All helper definitions have actual data; the comparison is a composite of the fixed
two-sided presentation, its normalized one-sided family, exact diagonal localization,
and the ordinary strict tensor identification. No arbitrary derived map or functorial
choice of resolutions replaces this construction.

The module uses the existing `TensorPresentation` record and the existing strict
reduction and termwise extension. The theorem produces the base computation record first and, separately, the
record for every slice. In particular it does not assume an object of the site
to obtain the base comparison when the site is empty. Universal representative computations and their equations
are packaged together so their choices are shared. Definitions `comparison`,
`extensionFirst`, and `extensionSecond` extract exactly the displayed isomorphisms.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The small site is `{C : Type c} [Category.{v} C] {J : GrothendieckTopology C}`.
  Coefficients live in `max c v r`, so no equality of site object and morphism
  universes is imposed. Sheafification and locally-bijective instances are the
  usual small-site infrastructure, not extra geometric restrictions.
* `R : Sheaf J CommRingCat.{max c v r}` is the commutative ring sheaf.
  `LocalizedStrictTensor.AlgebraTowers R` is the existing strict functor
  `ℕᵒᵖ ⥤ Under R`; the object `op n` represents positive level `n+1`.
  `algebraModules R` forgets to the actual underlying R-module sheaf by scalar
  restriction. Thus the coefficient maps are unital R-algebra maps.
* `TowerComplex R` consists of complexes in the category of strict towers. Its
  derived category is the localization of this category, not a functor category
  valued in a derived category. `diagonal R` is the actual constant functor, and
  `derivedReduction R t S` applies its exact derived functor before derived tensor.
* `BaseTensor R` and `TowerTensor R` specialize the dependency's
  `KFlatFixedTensor.TensorPresentation`, retaining its homotopy tensor, comparison
  from the ordinary total tensor, derived bifunctor, and specified two-sided
  comparison on flat-term K-flat representatives. `OneSidedConditions.normalized` identifies
  its family on two resolving objects with the inverse of this fixed comparison;
  `OneSidedConditions.natural_first` and the family's naturality retain both variables.
* `baseProperty` uses the recorded `LocalizedStrictTensor.Resolving`, hence
  `CochainComplex.IsKFlatIndependentCoefficients` and `IsFlatOnSite`.
  `ResolvingTower` is the same acyclic-total-tensor criterion on strict diagrams
  together with levelwise term flatness, namely the transported diagram-site
  predicate; `towerProperty` applies it to the represented homotopy complex.
  `Good R P` is exactly the two hypotheses on P and its constant diagram.
* `coefficient R S` is the actual degree-zero complex of the underlying module
  tower. `strictComplex` and `strictHomotopy` use `StrictReduction.reduction`
  through the recorded `LocalizedStrictTensor.reduction`. Degreewise this is
  P tensor S_n, with differential d_P tensor 1 and the actual tower transitions
  1 tensor s_n. `strictMap a` is the homotopy transformation induced by the
  recorded `reductionFamily.map a`, whose components are 1 tensor a_n.
* `OrdinaryModel.chain P` is an isomorphism of strict complex towers. Its `natural`
  field is the naturality equation in every cochain map; the datum is equivalently
  a natural isomorphism. It is not a family of levelwise derived isomorphisms. Its `pure` equation identifies the
  (i,0) total-tensor summand with the ordinary tensor generator. This includes
  the given strict transitions before localization.
* `comparison` is the displayed c_(P,S): it tensors the exact-diagonal localization
  isomorphism with the identity of S[0], applies the normalized one-sided family,
  and localizes `theta`. `Computation.theta_normalized` identifies theta on every
  chain complex with `OrdinaryModel.chain` through the homotopy comparisons.
* `Computation.natural_first` quantifies over every homotopy-category map of good
  representatives. `natural_coefficient` quantifies over every algebra-tower map
  and uses the actual `coefficientMap` and `strictMap`.
* `OrdinaryEvaluation.chain` compares the total tensor and its level evaluation;
  `natural` is its naturality equation for every pair of cochain maps.
  its `pure` equation says that the map is identity on local pure-tensor
  generators of every total-degree summand. Since these are strict tower maps,
  these evaluation identifications commute with transitions before localization.
* `Evaluation.homotopy_normalized` identifies the homotopy comparison with that
  ordinary map. `Evaluation.normalized` is the fixed two-sided representative
  square, using the fixed `resolvingComparison` components and the exact-evaluation
  homotopy-localization factors. Together with `homotopy_normalized`, this is
  the representative square of `TensorPresentation.representativeIso`. `Computation.evaluation_normalized` is the corresponding
  one-sided square with an unrestricted coefficient tower. Composing this square
  with the displayed factors of `comparison` gives the node's evaluated c_(P,S)
  equation, including the exact diagonal and evaluation conjugations.
* In the slice section, `V : C`, `R.over V`, `sliceAlgebras R V`,
  `localizedSystemExtension R V`, and `towerExtension R V` are the recorded
  localized ringed site, restriction, exact module extension, and termwise exact
  tower extension. `extensionFirst` requires `Good R (j_! P)`;
  `extensionSecond` requires `Good (R.over V) P`. Together these are precisely
  the four stated flat-term K-flat hypotheses, with no assumed preservation of
  K-flatness by extension. The first map is reduction of the exact j_! factor
  followed by c_(j_!P,S). The second is derived termwise extension of c_(P,S|V)
  followed by its exact factor. Their naturality follows from the same recorded
  naturality equations and the natural exact factors. Their evaluated
  normalization uses `evaluationExtensionDerived`, the canonical localization
  of the ordinary termwise identity, and the base/slice normalized equations.
* There is no hypothesis on flatness, K-flatness, or boundedness of the algebra
  tower, nor on surjectivity of any transition. All complexes are unbounded.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`.
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
* `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  `CochainComplex.ιMapBifunctor`, `Functor.map₂CochainComplex`.
* `Mathlib.CategoryTheory.Functor.OfSequence`: strict inverse functors and maps;
  `Functor.ofOpSequence` is the recorded inverse-sequence encoding.
* `Sheaf.CategoryTheory.DiagramSiteRealization`:
  `CategoryTheory.exists_diagramSite_realization`, including normalized
  module equivalence and exact evaluation (also used in the proof plan).
* `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.siteDerivedTensorIndependentCoefficients` and the resolving
  representative comparison of its existence theorem, packaged by the existing
  tensor-presentation interface below.
* `Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization`:
  `SheafOfModules.site_one_sided_tensor_normalization` (its two-sided normalization
  and two naturality equations are retained in the computation record).
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `SheafOfModules.overMap`; these underlie restriction.
* `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `SheafOfModules.localizedSystemExtension` and its additive/exact instances.
* `Sheaf.Paper.ReductionPullbackDerivedTower`:
  `CategoryTheory.StrictReduction.reduction`, `CategoryTheory.StrictReduction.termwise`.
* Already landed node `def-sf-localized-strict-tensor-comparison-data`, module
  `Sheaf.Algebra.Homology.LocalizedStrictTensorData`: `Modules`, `AlgebraTowers`,
  `algebraModules`, `reduction`, `reductionFamily`, `sliceAlgebras`, `Resolving`,
  `towerExtension`, `evaluation`, `pure`, `evaluationExtensionDerived`, and the
  standard derived-category and exactness instances.
* Already landed node `lem-weil-pbc-kflat-fixed-tensor-triangulated`, module
  `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`:
  `SheafOfModules.KFlatFixedTensor.TensorPresentation` and
  `TensorPresentation.representativeIso`. The ordinary total tensors use
  Mathlib’s canonical `curriedTensor` and `map₂CochainComplex` directly.

The last two already landed nodes are added to stmt_deps to cite their reusable
interfaces. The two missing computation interfaces are added as the new definition
nodes described below. There are no repaired dependency modules and no changes to
the item's statement or proof. All definition data is written in full. The ordinary
records give component isomorphisms and all naturality equations, equivalently
natural isomorphisms; the derived records retain the exact fixed normalizations.

Edge cases checked mathematically: zero ring, zero complex, empty site, unbounded
complexes, n=0 (the first positive tower level), nonflat coefficients such as
Z/2 over Z, nonsurjective transitions such as the unital map Z[t] to itself sending
t to t², nonconstant algebra towers, all coefficient-tower maps, arbitrary homotopy
maps (not only literal chain maps), and slice objects with multiple arrows to V.
The extension hypotheses are required separately; no preservation shortcut is used.
No derived-evaluation faithfulness is asserted. No statement fault or dispute found.

Searches for an existing declaration (before writing):

* `msearch.py ... leanfinder`: “A derived tensor product of a constant strict inverse
  sequence with a sheaf algebra tower is computed on a K-flat complex by termwise
  tensor, naturally and compatibly with evaluation”. Results included
  `HomologicalComplex.HasTensor`, `HasGoodTensor12`, `HasGoodTensor23`,
  `Sheaf.tensorProd_isSheaf`, and Tor object computations. None states this
  unbounded normalized strict diagram comparison.
* `msearch.py ... loogle`: `"DerivedCategory", "tensor", "evaluation"` returned
  zero hits.
* `msearch.py ... grep` on CategoryTheory:
  `(tensor|Tensor).*(evaluation|Evaluation)|(evaluation|Evaluation).*(tensor|Tensor)`.
  Ten hits concerned external products, monoidal limits, rigid evaluation, and
  Cartesian functor categories; none was this statement.
* `msearch.py ... leansearch`: “The derived tensor of a constant diagram with a
  strict tower of sheaf algebras is computed by termwise tensor on a K-flat complex
  and commutes with exact evaluation”. Hits included flat-module tensor exactness,
  tensor associativity/commutation, `CategoryTheory.constantCommuteCompose`,
  under-category limits, equalizers, and `HomologicalComplex.tensorObj`; no match.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and proposed
  namespace/declaration found no existing statement. Tensor/evaluation searches
  found specialized affine/open models and the localized strict tensor interfaces;
  the latter are reused, not copied. Relevant full signatures and docstrings were
  opened, including the generic tensor-presentation record and its actual maps.

Source checks: Stacks sites-cohomology.tex around definition-derived-tor, Tag 06YU,
including the preceding one-sided construction with arbitrary second factor;
derived.tex Tag 015F, lemma-right-derived-exact-functor. The Lean theorem docstring
retains all seven DAG proof steps and their cited dependencies.

All three delivered modules compiled cleanly through the prescribed `scompile.py`
wrapper on 2026-10-22. The ordinary, derived-data, and theorem library checks took
43.6 s, 41.1 s, and 35.8 s respectively. There are no compiler errors or warnings;
the theorem is the sole postponed proof. The corrected empty-site quantification also compiled cleanly (35.8 s).
The first preflight required individual bracket citations in the two new nodes;
all grouped citations were expanded to the prescribed individual `[id]` form.
The repeated `deliver2.py ... --no-push` returned OK: preflight and every
per-file compile passed on 2026-10-22 (dry-run commit da7610f4dd4).

## Second reading by NK

This is the dispatcher's single-worker delivery; no independent second worker is
claimed. The maintainer performs the independent review specified in the brief.
The worker's final rereading includes both new definition nodes and modules and
uses the complete clause correspondence above and
checks that c is the specified composite, pure tensors fix ordinary evaluation,
coefficient maps and strict transitions use actual functors, and slice extension
requires all four resolving hypotheses. Self-check found and repaired the initial
constant-diagonal opacity at local generators, a product-morphism syntax mismatch,
and repeated expensive conversion of uncurried tensor functors. These were
elaboration or compilation repairs; the natural-language statement is unchanged.
The final rereading also caught an outer slice-object binder that made the base
conclusion vacuous on an empty site. Slice quantification is now inside the
second conjunct, so the base computation holds independently of any slice object.
The source statement is unchanged; there is no remaining statement dispute.

## New nodes

`def-sf-strict-tensor-ordinary-model-data`, module
`Sheaf.Algebra.Homology.StrictTensorOrdinaryData`, defines the actual ordinary
complexes, their local total-tensor generators, and the comparison-data records
`OrdinaryEvaluation` and `OrdinaryModel`. Each record contains component cochain
isomorphisms, the full naturality equation, and its pure-tensor normalization;
neither asserts existence. Sources are Stacks 03EK, 03CY, 06YM and 06YU and the
item's proof Steps 1–2 and 6. The new LeanSearch query returned Dold–Kan, shifts,
tensor equalizers and single-functor comparison results. LeanFinder returned
ordinary tensor inclusions and monoidal-sheaf infrastructure, which are reused.
The Mathlib Algebra/Homology grep found no strict-tensor matches; blueprint search
found no matching node. Project searches found no such record; the similarly named
`CompletionUnit.OrdinaryModel` was opened and concerns completion units and inverse
limits for quotient-coefficient systems on a pro-etale site. The existing localized
comparison and linear-evaluation nodes were read and concern universal reduction
counits and coefficient-linear projection comparisons, not these ordinary total-tensor
and evaluation maps. Raw search results are retained in the new node's
`mathlib_searches`. The node cites all existing tensor, module and strict-tower data.

`def-sf-strict-tensor-derived-evaluation-data`, module
`Sheaf.Algebra.Homology.StrictTensorDerivedData`, defines resolving properties using
the recorded base predicate and its diagram acyclic-tensor characterization, the
existing fixed `TensorPresentation` interfaces, one-sided families and their two-sided
normalization conditions, evaluation representative squares, and the explicit comparison
composite. Its intermediate `Evaluation` record fixes the evaluation maps and both
normalizations. The main `Computation` record adds the unrestricted one-sided evaluation
square and naturality in both variables; no existence is asserted by this definition. Sources
are Stacks 06YN, 06YS, 06YU, 07A4 and 015F and the item's proof Steps 3–6. LeanSearch
returned flat-module tensor exactness results; Loogle found standard `Lifting₂`
bifunctor-localization declarations, and the Mathlib grep found no one-sided or
representative-comparison record. DAG and project searches were the same explicit
searches described above, with no matching interface. The existing tensor-presentation
record is reused, not redefined. Its `mathlib_searches` preserves the actual queries
and returned declarations. It depends on the ordinary-data node and already landed
interfaces, and the item cites both new nodes; this introduces no dependency cycle.

The original single file exceeded the compile limit despite individual interface
repairs. The two missing notions now have their own definition nodes and owning
modules under §1(A). The derived-data module owns the aggregate computation datum;
the item module states existence and constructs the two slice-extension composites.
Naming the uncurried total tensor functors and generic coherence squares avoids
repeated expensive conversions. The source statement is unchanged.

The additional computation-data search used LeanSearch and LeanFinder with the exact
query “Normalized strict tensor computation data with one sided two sided K flat
comparison ordinary model exact evaluation and coefficient naturality”. Results were
flat-module tensor exactness and free-monoidal coherence, with no such record.
The Mathlib grep `strict.*tensor|tensor.*strict` on Algebra/Homology had zero hits,
and blueprint search “strict tensor computation” had zero matches. Project searches
found unrelated `Computation` records for pro-etale open quotient reductions, condensed
equivariant bar resolutions, and simplicial derived colimits; their full signatures
and docstrings were opened. None supplies this general ringed-site interface.
