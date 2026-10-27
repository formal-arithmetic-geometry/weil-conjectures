## Worker report

The module Sheaf.Algebra.Homology.CoefficientLinearProjectionDescent states
`SheafOfModules.CoefficientProjection.coefficient_linear_projection_descent`.
Its sole postponed theorem has proof `by sorry`. Four definitions merely name
normalization equations and compose existing natural isomorphisms; none choose
objects or contain postponed data or proofs. Each declaration belongs to this
node and carries its source and blueprint docstring. The theorem docstring gives
all seven proof steps, including the independent normalization of scalar
restriction and the final uniqueness among arbitrary natural transformations.

Hypotheses and objects, clause by clause:

- The site is `C : Type c`, `Category.{v} C`, `J : GrothendieckTopology C`;
  coefficients and modules live in `max c v r`. The base and slice sheafification
  and locally-bijective-equivalence instances express the ordinary module sheaf
  categories. No object/Hom universe equality is imposed.
- `R : Sheaf J CommRingCat` is the given ring. `V : C` is the slice object.
  `S : Under R` bundles the target ring `S.right` and its unital map `S.hom`.
  `sliceAlgebras R V` is the actual ring/map restriction to `J.over V`.
- `Modules`, `D`, `ring`, and `localizedSystemExtension` are existing transparent
  names for the dependency module categories, ordinary unbounded localizations,
  underlying ring sheaves, and actual sheafified direct-sum extension. Their
  exact-extension comparisons are `mapDerivedCategoryFactors`.
- `e` and `eV` are the existing `ScalarModel` presentations. Their E fields are
  sheafified sectionwise scalar extension, fixed on objects AND maps. Their T
  fields are its universal left derived functor; epsilon is its specified
  computation counit. Thus these parameters unpack derived change of rings;
  they are not arbitrary replacement maps or new hypotheses about flatness.
- The natural iso `theta` is the inverse of the node's kappa. Its source is
  restriction followed by R-extension and its target is S-extension followed
  by restriction. `hθ : ScalarExtensionNormalized ... θ` says that the same
  section in the same direct-sum summand is preserved, using the actual
  extension-presheaf/sheafification generators. This inverse orientation is
  equivalent to kappa preserving those generators.
- `η` is a natural isomorphism `j_R! ⋙ e.E ≅ eV.E ⋙ j_S!`. It belongs to functors
  valued in S-module sheaves, so every component is S-linear. As in the node,
  no generator normalization is imposed on eta itself.
- `A, AV, a, aV, ha, haV` specify the underlying right-sided derived tensor
  presentations and their computation maps. Precisely, their ordinary functors
  are `e.E ⋙ scalars` and `eV.E ⋙ scalars`, NOT arbitrary endofunctors.
  `ha` and `haV` are their universal left-derived properties.

Why this last presentation is the node's derived tensor (no statement correction):
`IndependentExtensionTensor.exists_extensionTensorComparison` identifies the
ordinary restricted scalar extension with tensor by the restricted target ring,
normalized on all pure tensors; symmetry puts that ring on the right, as the
node does. Applying these functors termwise is therefore exactly tensor by the
ring in degree zero, using the standard degree-zero total identification.
On flat-term K-flat representatives this computes derived tensor by
`site_one_sided_tensor_normalization`, even when the target ring is nonflat.
Resolving localization gives its universal left-derived pair. Conversely every
pair specified by `ha` is uniquely counit-compatibly isomorphic to that pair.
Quantifying over presentations retains the specified computation transformation
rather than choosing a new derived tensor or a second monoidal structure.
In particular `a, aV` are the one-sided comparisons BEFORE and independently of
beta. This is equivalent presentation data for the functors in the node, not a
hypothesis giving the desired comparison. There is no assumed comparison between
`j_R! ⋙ A` and `AV ⋙ j_R!`.

Conclusions, clause by clause:

- The existential `β` is the natural S-linear derived isomorphism
  `j_R!.mapDerivedCategory ⋙ e.T ≅ eV.T ⋙ j_S!.mapDerivedCategory`.
- `LinearNormalized` gives its exact representative equation for EVERY
  `P : CochainComplex ... ℤ` satisfying `Resolving`. It composes ambient scalar
  counit after the exact-extension comparison, then Q of the actual termwise
  eta. The other side is beta then slice counit then exact S-extension comparison.
  This is exactly conjugation by the specified a_P and b_P, without hiding the
  representative comparison behind a bare Nonempty isomorphism.
- `∀ β', LinearNormalized ... β' → β' = β` is uniqueness with that normalization.
- The existential `x, y` identify restricted derived scalar extension with the
  separately specified tensor functors. The next two equations characterize
  these identifications by the scalar counits and exact-restriction comparisons.
  They quantify over all complexes, hence in particular every resolving complex.
  Neither equation refers to beta or to the projection comparison.
- `ordinaryUnderlying` is eta followed by kappa on ordinary modules.
  `NatIso.mapHomologicalComplex` makes its actual degreewise cochain map r_P.
- `underlyingComparison` is x inverse, restricted beta, derived kappa (the
  inverse of `scalarExtensionDerived ... theta`), then extended y. All four
  factors are concrete compositions of the existing natural isomorphisms.
- `UnderlyingNormalized` says A_P followed by Q(r_P) equals rho followed by B_P.
  The theorem asserts this for `underlyingComparison.hom`.
- The final quantifier covers EVERY natural R-linear transformation rho',
  without assuming invertibility, satisfying the same representative equation.
  It equals the restricted beta under the independently normalized x and y.
  In particular it applies to strict-tower evaluation with those computations;
  the conditional tower clause introduces no additional unconditional assertion
  that evaluation computes a derived functor.
- All complexes are integer indexed and unbounded. There is no flatness of
  S over R, no boundedness, no completeness, and no tower-transition hypothesis.

Dependencies used (module and declarations):

- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`, Q and Qh.
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients:
  `CochainComplex.IsKFlatIndependentCoefficients` (through Resolving).
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite: `IsFlatOnSite`
  (through Resolving).
- Mathlib.Algebra.Homology.BifunctorShift and
  Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses give the existing
  total tensor and sheaf tensor used by the presentation models.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous and
  Mathlib.CategoryTheory.Sites.Over: `overFunctor`, `Sheaf.over`, `J.over`.
- Sheaf.CategoryTheory.LocalizedModuleExactForSystems:
  `localizedSystemExtension`, its exactness/additivity instances.
- Sheaf.Paper.RingedTopoiDerivedPullbackIndependent:
  `ringedTopoiDerivedPullbackIndependent`, universal counits on K-flat models.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings: `restrictScalars`.
- Sheaf.Paper.RestrictionDerivedProducts: exact derived scalar restriction.
- WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf:
  `extensionByZeroPresheaf`, via extensionSection and localizedSystemExtension.
- Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization:
  `site_one_sided_tensor_normalization`, the unrestricted-other-factor computation.
- Sheaf.Algebra.Homology.LocalizedStrictTensorData: the existing `Modules`, `D`,
  `Resolving`, `scalars`, `ScalarModel`, `sliceAlgebras`, `ScalarExtensionNormalized`,
  `scalarExtensionDerived`, `scalarComparisonOnComplexes`, `extensionSection`.
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel:
  `DerivedChangeOfRingsCochainModel` (via ScalarModel).
- Sheaf.Algebra.Homology.ExtensionTensorComparisonIndependent:
  `IndependentExtensionTensor.exists_extensionTensorComparison`.
- Sheaf.Algebra.Homology.RingedOpenFlatResolution:
  `ringedOpen_preserves_flat_resolution` (proof import).
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor:
  `mapDerivedCategory`, `mapDerivedCategoryFactors` and their natural iso maps.
- Mathlib.CategoryTheory.Localization.Predicate: `Localization.liftNatIso`,
  `fullyFaithfulWhiskeringLeft` and `natTrans_ext` (proof import).

The two already landed definition nodes for comparison data and cochain scalar
models are added to stmt_deps, as authorized. Their source declarations and full
interfaces were read. No dependency is rewritten, and no new DAG node is needed:
the four local helpers package the given node's equations, not independent notions.

Edge cases checked: zero ring and zero complexes; the empty site (the V binder
then has no instances); objects with no map to V (the extension sum is empty);
multiple maps to V (hθ quantifies over every summand); identity and arbitrary
nonflat ring maps; negative degrees and complexes unbounded in both directions.
No nonzero, nonempty, flatness, positivity or boundedness binder excludes any case.
All universes and variables are bound explicitly; autoImplicit is disabled.

Searches: msearch LeanFinder query "Coefficient linear derived slice projection
comparison with unique K flat representative normalization" returned unrelated
flat-module facts, no match. Loogle query `"Localization", "NatIso"` returned
`Localization.liftNatIso` and its bifunctor variants: generic descent only.
LeanSearch query "A coefficient linear ordinary slice projection isomorphism
descends uniquely to derived module sheaves using K flat complexes" returned
localization/quasi-iso and K-projective facts, no match. msearch grep query
`(derived|Derived).*(extendScalars|restrictScalars)|(extendScalars|restrictScalars).*(derived|Derived)`
returned no Mathlib hits. Searches in lean/WeilConjectures for projection/descent
and coefficient/linear, and the exact blueprint id, found no statement of this
node. Searches in lean/Sheaf found LocalizedStrictTensorData and LinearEvaluation:
these provide reusable presentation definitions, but the latter is conditional
comparison data for towers, not existence/uniqueness of this comparison. Full
signatures and docstrings of the recorded interfaces were read before use.
Search wrappers recorded their exact queries/results in searches.jsonl.

No STATEMENT-DISPUTED or source fault was found. The source text read was
sites-cohomology.tex, definition-derived-tor and lemma-j-shriek-and-tensor,
together with the node's seven-step coefficient-linear refinement.

## Second reading by Q59

A fresh in-thread comparison of the node, its proof and the module found the
following elaboration issues, which were fixed: implicit presentation universe
arguments were ambiguous under max; all occurrences now give explicit universe
parameters. Termwise comparison needed the additive instances explicitly in the
normalization definition; these are the existing model and exact-extension
instances. No extra assumption was added. The final scalar uniqueness covers
arbitrary natural transformations, while beta uniqueness covers natural isos,
matching the node. Both identifications x and y have independent counit equations,
so the scalar representative identity is not imposed by defining y from beta.
Theta has the inverse orientation to kappa and its generator equation is exactly
the inverse generator identity. The universal-pair tensor presentation preserves
the node's one-sided normalization and nonflat-ring case as detailed above.
This is an in-thread second reading; the maintainer performs the independent
review required by the dispatched-worker workflow.
