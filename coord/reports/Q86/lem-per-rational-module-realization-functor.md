## Worker report

The module `Sheaf.Paper.RationalModuleRealizationFunctor` states
`AlgebraicGeometry.Scheme.rationalModuleRealizationFunctor`, with proof `sorry`.
Its conclusion is `Nonempty (RationalModuleRealization l E X)`, a package of the
specified coefficient identifications and the raw rational realization. Three small
canonical helpers implement the lifted integer inclusion, the constant-section map
to rational functions, and the ordinary constant rational module model. Their data
are explicit ring homomorphisms, sheafification adjunction, and compositions of the
existing constant-module and scalar-extension functors. No theorem is proved here.

Read source: Bhatt--Scholze, The pro-etale topology for schemes, PDF pages numbered
58--62, Lemma 6.8.2, Definitions 6.8.3/6.8.6/6.8.8/6.8.10, Proposition 6.8.11(3),
Proposition 6.8.14(2), Remark 6.8.15. The assertion is only the construction portion
of the equivalence in 6.8.14(2).

Hypotheses and clauses, checked against the node:

- Prime ell is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  `PbcIntegralRing l E`, `pbcIntegralDatum l E`, and `pbcUniformizer l E` reuse
  the recorded valuation ring and its chosen uniformizer, lifted to `u+1`.
- The scheme and geometric assumptions are `(X : Scheme.{u}) [IsNoetherian X]`,
  `Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)`, and
  `Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))`. Fact only packages the
  stated assumptions for the existing raw-rational triangulation instances.
- The small site is `ProEt.topology X`; its object universe remains `u+1` and
  its morphism universe `u`. Coefficient rings and module carriers are `u+1`.
- The completed ring is `pbcAdicCompletion X (pbcIntegralDatum l E)`, and its
  finite quotients are `pbcAdicRings`, indexed by `n : ℕ` for exponent `n+1`.
  `integralIso`, `finiteIso`, `finite_normalization`, and `integral_normalization`
  specify the function-sheaf identification and quotient projections, including
  the normalization on constant sections through `integralCoefficientULift`.
- The rational ring is `rationalCoefficientSheaf l X E`. `localizationIso` and
  `localization_normalization` identify it with the existing sheaf localization.
  `inclusion` and its normalization specify the scalar map on continuous functions.
- `restriction` gives integral and rational coefficient isomorphisms for every
  locally closed immersion, fixes them by the existing restriction-normalization
  predicates, and gives the scalar compatibility square.
- `ordinary_exact` is finite-limit and finite-colimit preservation of the actual
  `pbcExtend (integralIso.hom ≫ inclusion)`. Its additivity is already inherited
  from the existing tensor functor. `derived_exact` asserts CommShift and
  IsTriangulated for the actual `pbcDerivedExtend` along that same map; this is F_X.
- `cohomology` is a natural isomorphism of functors for every `r : ℤ`, with left
  side F_X followed by the recorded derived cohomology functor and right side
  cohomology followed by ordinary extension of scalars.
- C_X is exactly `PbcBoundedConstructibleComplete X (pbcIntegralDatum l E)`.
  Its underlying predicate retains intrinsic completeness, uniform reductions,
  and compatible etale-origin witnesses; no replacement category is introduced.
- `constructible` asserts a lower and upper integer cohomology bound for every
  integral object and, for every cohomological degree, a finite locally closed
  scheme stratification on which inverse-image cohomology is finite locally free.
  `FiniteLocallyClosedStratification` is the recorded finite partition interface.
  `IsFiniteLocallyFree` uses actual pro-etale local module trivializations; the
  inverse-image coefficient ring is identified with the stratum coefficient ring
  by `restriction`.
- R_X and Q are the existing `PbcRationalCategory` and `pbcRationalization`, with
  raw localized Hom modules and unchanged integral objects. `J` has this source
  and the ambient derived rational module category as its target.
- `objects` is J(QK)=F(K). `fractions` is J(f/varpi^n)=varpi^(-n)F(f), with
  `eqToHom` transports for the object equalities. The denominator on the left
  is the inverse field power transported through `pbcRationalCoefficientEquiv`.
  At n=0 it is precisely the factorization formula on integral morphisms.
- `moduleLinear` and `scalar_normalization` specify the E-action on rational
  module morphisms by actual constant sections. The derived category inherits
  that action from Mathlib; `linear` is `J.Linear E`, and `additive`, `shift`, and
  `triangulated` express the remaining functor properties. The action is fixed,
  not an arbitrary unconstrained linear structure.
- `models` identifies localization of `integralConstantModule ... N` with
  `rationalModuleConstantModel ... (E tensor_A N)` for every finitely presented
  N. `ModuleCat.extendScalars rationalModuleIntegerInclusion` is E tensor_A N;
  `Module.Finite` and `Module.Free` express its finite free field model. No
  flatness or torsion-free assumption occurs. Inverse image and restriction to
  any covering object transport this ordinary tensor identity to a local model;
  normalized coefficient restriction identifies its ring with E_S.
- No full faithfulness, essential surjectivity, or equivalence is asserted.

Dependency declarations read and used (their recorded source modules were opened):

- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and its imported sheafified tensor.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `...HomologySequence`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.homologyFunctor`.
  The recorded `SfCommonStageWeilCohomology` uses this same cohomology machinery;
  it is imported as recorded, while the general module cohomology is Mathlib's.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its coefficient
  import: `Padic.coefficientExtensionIntegers`, `...Uniformizer`, finite quotients.
- `Mathlib.CategoryTheory.Linear.LinearFunctor`: `Functor.Linear`;
  `Mathlib.CategoryTheory.Triangulated.Functor`: `Functor.IsTriangulated`.
- `Sheaf.Paper.AdicCoefficientDatum`: datum and normalized completed coefficients;
  `Sheaf.Paper.IntegralUniformCoefficient`: the full integral coefficient category;
  its existing `BoundedConstructibleComplete` import supplies the unchanged
  `PbcIsBoundedConstructibleComplete` predicate and `pbcIntegralDatum` encoding.
- `Sheaf.Paper.ContinuousConstructibleModule`:
  `ProEtale.continuousCoefficientModule`, `IsContinuousConstructible` local model
  conventions. Over E finitely presented models are locally finite free, rendered
  here directly by the existing finite locally free predicate.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcRationalization`;
  `Sheaf.Paper.PbcScalarExtension` supplies existing rational triangulation and
  field-action instances; it is not used to assume a realization equivalence.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` (SheafOfModules).
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel`, its normalized ordinary and derived functors;
  the published `pbcExtend`/`pbcDerivedExtend` expose the same tensor construction.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`:
  `continuousCoefficientImmersionRestriction` and its normalized coefficient
  isomorphisms; `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralConstantModule`, `integralCoefficientULift`,
  `integralStratifiedPerfectCharacterization` and its closure statement.

All already-stated proof dependencies are imported explicitly, including Mathlib's
exact derived factorization, linearity, and cohomology comparison modules. The
constant finite-presentation extension and local derived restriction comparison
nodes currently have no Lean attachment; their proof plans are named in the
complete eight-step theorem docstring, as in the item's proof.

Searches actually run with msearch.py for this item:

- leanfinder: "Scalar localization of completed integral constructible sheaves gives
  a rational triangulated functor with constructible cohomology": eight generic
  triangulated localization and derived-bound hits, no exact statement.
- leansearch: "rational scalar localization functor derived constructible sheaves":
  eight hits (finite-presentation localization, linear Q, generic localization),
  none states the completed-coefficient construction and all its clauses.
- loogle: "CategoryTheory.Functor.mapDerivedCategory": twelve hits for exact
  derived functors, shift and linearity structures; these are used as machinery.
- grep: "constructible.*localiz|localiz.*constructible": zero Mathlib hits.
- rg over `lean/WeilConjectures`, `lean/Sheaf`, and upstream-name records for
  rational realization, plus the exact item id: no exact existing attachment.
  The older `ContinuousRationalDerivedRealization.At` combines realization with
  full faithfulness, an exact essential image, t-structure and other comparisons;
  binding that stronger package would not state this node. Reusable scalar and
  coefficient APIs were checked. The final module does not import that package.

Edge cases checked: the empty scheme is not excluded (no Nonempty assumption),
zero cohomology and empty stratifications are allowed; all r in Z and denominator
n=0 are included; N=0 and N=A/varpi^k give rational rank zero, while
N=A^r plus torsion gives rank r. No single denominator for a section over an
arbitrary non-quasi-compact object is required. The localization is sheafified.

No statement correction, new DAG node, dependency repair, or disputed statement.
Every variable and universe is explicit (`autoImplicit false`). All declarations
have source/blueprint docstrings and the theorem has the complete eight-step proof.
The module compiled cleanly through scompile.py (sandbox and library path), with
only the expected sorry allowed. An initial import of the large parent realization
hit a timeout in an unrelated overlay dependency; it was removed in favor of the
smaller foundational interfaces and an explicitly normalized field-action field.

## Second reading by Q86

No second worker reading is claimed. The dispatcher requires this worker to deliver
directly without spawning other agents; the maintainer supplies independent review.
A final self-check re-read the exact node and every field of the package, including
constant-section normalization of the field action and the n=0 fraction case.
