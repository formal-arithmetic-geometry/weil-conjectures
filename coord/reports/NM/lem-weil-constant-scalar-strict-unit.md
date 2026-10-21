## Worker report

The module `Sheaf.Paper.ConstantScalarStrictUnit` states
`WeilConjectures.ConstantScalarStrictUnit.regular_scalar_strict_unit` with proof `sorry`.
It retains the source's finite-field datum, prime inequality, finite coefficient extensions,
small pro-etale site, completed coefficient sheaves, quotient maps, scalar-extension tower,
termwise products, strict mapping cocone, and module-sheaf derived categories. The helper
abbreviations and definitions are only names for existing constructions: `regularComplex`
is the single regular complex `R_E[0]`; `finiteRegularComplex` is the finite regular complex;
`regularSection` and `finiteZeroIso` are the canonical degree-zero single-complex maps;
`boundary` is the existing tower endomorphism; `coordinate`, `quotientCoordinates`,
`unitCoordinates`, and `zeroSecondComponent` spell out the cone projections and their
normalization. No tensor, completion, scalar-extension, reduction, or Roos construction is
copied.

The first conjunct `integralOperationsGoodComplex ... regularComplex` renders K-flatness
and flatness of every term. `finiteMultiplication` renders the family of finite-level
isomorphisms, the multiplication formula on every site section and every pair of sections,
the inverse formula on every section, and compatibility with each reduction transition.
`finiteDerivedComputation` is invertibility of the existing derived scalar-extension
counit on the regular complex. `reductionUnits` gives, for every level, the strict finite
reduction isomorphism, its unit-section formula, its equality with the canonical projection
complex, and the corresponding localized equality for every K-flat resolution witness.
The `∃!` clause gives a chain map from `R_L[0]` to the strict scalar tower whose every
quotient coordinate is `1 ⊗ π_m(s)` and whose shifted cone component is zero; uniqueness is
of the map satisfying both clauses. The final equivalence states that checking the first
coordinate only on the unit section is equivalent to checking it on all sections.

Dependencies used (all imported by their recorded module):

- `WeilConjectures.FiniteFieldDatum` from `Sheaf.Paper.FiniteFieldFiber`;
- `Padic.finite_coefficientExtensionRing` from
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`;
- `AlgebraicGeometry.Scheme.ProEt` and `AlgebraicGeometry.Scheme.ProEt.topology` from
  `Mathlib.AlgebraicGeometry.Sites.Proetale`;
- `WeilConjectures.completedIntegralCommRingProjectionUnrestricted` and the completed
  coefficient constructions from `Sheaf.Paper.CompletedIntegralCoefficients`;
- `WeilConjectures.integralScalarRho`, `integralScalarFiniteComplex`,
  `integralScalarTensorSection`, `integralScalarTransition`, and
  `integralScalarComplexFunctor` from `Sheaf.Paper.IntegralScalarExtensionWellDefined`;
- `WeilConjectures.integralScalarExtensionOfUniverses` from
  `Sheaf.Paper.IntegralScalarExtensionUniverses`;
- `WeilConjectures.canonicalIntegralReductionTowerMap` from
  `Sheaf.Paper.IntegralReductionTowerCanonical`;
- `WeilConjectures.unrestrictedTowerFiniteComplex`, `unrestrictedTowerTensorSection`, and
  `unrestrictedTowerUnit` from `Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted`;
- `WeilConjectures.integralOperationsGoodComplex`,
  `integralOperationsFiniteModules`, `integralOperationsTowerStep`, and
  `integralOperationsRoosFunctor` from `Sheaf.Paper.IntegralOperationsWellDefined`;
- `CochainComplex.IsKFlatIndependentCoefficients` and the independent tensor APIs from
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`;
- `SheafOfModules.IsFlatOnSite` from `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`;
- Mathlib's `DerivedCategory`, `CochainComplex.mapBifunctor`, single-complex maps, and
  `CochainComplex.mappingCocone`.

Edge cases checked: the index starts at `n = 0`, representing exponent one; all site
objects and all sections are quantified, including an empty site or empty scheme; no
nonempty-site or surjectivity hypothesis is added; the zero complex terms are included by
the `∀ i : ℤ` cone condition; the unit-only condition includes the degenerate case
`1 = 0`; and the full coefficient and scheme universes remain independent.

Searches for an existing statement or definition: `msearch.py ... leanfinder` with the
regular completed coefficient scalar-tower query (hits only generic sheaf presentation,
adic-completion, and flatness declarations; no match); `msearch.py ... loogle
'CochainComplex.mappingCocone.lift'` (generic mapping-cocone constructors only);
`msearch.py ... leansearch` with the normalized strict scalar-unit query (generic mapping
cone and Moore-complex results only); `msearch.py ... grep 'mappingCocone|unitHomEquiv'`
(Mathlib mapping-cocone and module-unit APIs only); `rg` over `lean/WeilConjectures` and
`lean/Sheaf` for the item id and regular scalar-unit names (no declaration of this node).
The source PDF was read at Bhatt--Scholze Definition 3.5.2 (p. 24) and Lemma 6.8.2(1)
(pp. 58--59). The module compiles with `scompile.py`; the only proof is the expected
`sorry`.

No `STATEMENT-DISPUTED` flag or node fault found.

## Second reading by NM

This is a fresh self-review of the node and module; no second agent was started, as
required by the dispatcher. The maintainer performs the independent review. The finite-field datum, prime inequality,
finite extensions, valuation rings and uniformizers are represented by the recorded
coefficient and finite-field declarations. The completed sheaf projections, scalar maps,
termwise tensors, transitions, product cone, and derived categories are exactly the
recorded objects. The K-flat/flat-term conjunct, multiplication and inverse equations,
transition equation, derived counit, identity-extension unit comparisons, strict map
existence and uniqueness, and unit-only equivalence all occur explicitly. No hypothesis is
added, no clause is dropped, and no edge case is excluded. The full file compiles cleanly.

Specific checks in this reading: the tensor API writes `z ⊗ r`, opposite to the
node's `r ⊗ z`, but its balanced change of rings is the identical extension and
multiplication is precisely `rho(r) * z`. The finite transition clause needs only degree
zero because both sides are isomorphic to single complexes; their terms at all other
degrees are zero. The inverse formula for the identity-extension finite isomorphism
uniquely fixes its multiplication inverse, so the strict and localized unit equations
refer to the specified isomorphism. The canonical map `projectionModule` is obtained by
regular-module linearity from the section one, so it is exactly the ring projection,
not an arbitrary linear map. Initial elaboration failures were repaired by selecting the
existing independent-size sheafification instance and by making the multiplication
carrier explicit; no universe constraint or statement correction was introduced.

The existing `constantCoefficientScalarUnit_existsUnique` in
`Sheaf.Paper.ConstantCoefficientScalarNormalization` states only the unit-coordinate
strict existence/uniqueness clause and restricts the scheme and coefficient universes to
be equal. It does not state this node's complete conjunction, so it is not an exact
existing-statement match. The new regular-complex abbreviation is the same Mathlib
single-functor construction, exposed at the already supported independent universe sizes.
The splitting of the conjunction into three named predicates reduced elaboration time
without changing its content; all delivered declarations remain in one module.
