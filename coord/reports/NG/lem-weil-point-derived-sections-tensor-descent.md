## Worker report

The module `Sheaf.Paper.PointDerivedSectionsTensorDescent` states
`WeilConjectures.point_derived_sections_tensor_descent`, with its sole proof `sorry`.
Its result structure spells out the complete assertion rather than replacing the
normalized comparison by an arbitrary derived isomorphism. The four abbreviations
`PointDerivedSectionsTensor.sectionsE`, `sectionsL`, `A`, `B` only name the recorded
evaluation functors and their composites. They construct no replacement ring, module
category, scalar functor or tensor product. All structure fields are data or properties
of the assertion, not assumptions in the main theorem.

Hypotheses and objects, clause by clause:

- The global datum is `(D : FiniteFieldDatum.{t})`. Its `D.k` is the fixed algebraic
  closure of its finite base field. `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)` states the
  coefficient-prime convention exactly.
- `(Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]` is the fixed
  algebraic closure of Q_l. `(E L : IntermediateField ℚ_[l] Ω)` with the two
  `FiniteDimensional` instances and `(h : E ≤ L)` are precisely the finite subextensions
  E subset L. Their map is `IntermediateField.inclusion h`; the valuation rings and
  their inclusion are the dependency's `Padic.coefficientExtensionIntegers` and
  `integralScalarIntegerInclusion`.
- The point is always `Spec (.of D.k)`. `integralTowerModules l E (Spec (.of D.k))`
  and its L counterpart are the recorded sheaves of modules over the inverse-limit
  completed coefficient ring sheaves, not modules over a discrete constant sheaf.
  `DerivedCategory`, `DerivedCategory.Q`, `QuasiIso`, and `mapHomologicalComplex (.up ℤ)`
  are Mathlib's unbounded localization and termwise constructions.
- The two module derived categories have independent chosen localization instances
  `HasDerivedCategory.{wE}` and `HasDerivedCategory.{wL}`. These are choices of
  presentation, not hypotheses on complexes or coefficient extensions. The sheaf
  derived categories use the existing published standard instances. The site has
  object universe t+1 and morphism universe t; coefficients/modules have size
  `max u (t+1)`. No equality of t and u or wE and wL is required.
- `(d : PointFiniteFreeSectionsTensorData ... )` is the finite-free comparison supplied
  by the statement dependency: the node says “let theta be the ... map specified in”
  that lemma. Its `constantE`/`constantL` fix the coefficient-section identifications;
  `d.complexes` is its termwise balanced comparison, fixed in each degree by
  `d.complexes_hom` and `d.comparison_tensor`. This datum is universally quantified,
  so the theorem applies to any presentation of that specified map. Its existence is
  the recorded `point_finite_free_sections_tensor` theorem, not an extra restriction.

Conclusions, clause by clause:

- `sheaf_quasiIso`, `module_quasiIso`, `sectionsE_quasiIso`, `sectionsL_quasiIso`
  state preservation of every quasi-isomorphism by the four termwise functors.
  The additive and finite-limit/finite-colimit structure fields assert exactness
  required to name Mathlib's canonical induced derived functors. They do not impose
  exactness as an input hypothesis. Additivity of the two tensor functors is already
  supplied by the published interfaces.
- `comparison` identifies the exact-functor descent of ordinary sheaf scalar extension
  with the actual `completedDerivedScalarExtension`, which is K-flat left-derived
  change of rings from the dependency. `comparison_counit` fixes its inverse on
  **every** representative by `completedScalarCounit`, after the specified ordinary
  factorization. `comparison_unique` says precisely that this normalization determines
  the natural isomorphism. No new derived extension or arbitrary map is selected.
- `localized` descends A to B as a natural isomorphism on the entire source derived
  category. `localized_representative` states its component is the localized
  `d.complexes.hom`, including the canonical factorization isomorphisms suppressed in
  the TeX. `localized_unique` characterizes it by these values.
- `theta` has literal source `(sectionsE d).mapDerivedCategory` followed by the module
  tensor descent, and target the published derived sheaf extension followed by
  `(sectionsL d).mapDerivedCategory`. Thus its components are exactly the displayed
  theta^D for all derived objects K. `theta_eq` fixes it as the localized balanced map
  followed by the comparison, with the canonical exact-functor composition
  isomorphisms. It is a natural isomorphism of functors, not only a family of
  cohomology isomorphisms or representatives.
- `resolution` quantifies **every** complex C, K-flat complex P, and quasi-isomorphism
  q:P→C with flat terms (`IsKFlatIndependentCoefficients` and `IsFlatOnSite`). It
  defines no chosen resolution and requires no degreewise surjectivity. Write
  rho_q = inv(LT.map(Q.map q)) followed by epsilon_P. The equation is
  theta_C followed by Gamma(rho_q), then the target sections factorization, equals
  inv(A_D(Qq)) followed by the source factorization and Q(theta_P). This is exactly
  the node's formula after cancelling Gamma(rho_q), which is invertible by counit
  normalization and localization of q. Both source sections/tensor and target tensor
  quasi-isomorphisms are the maps in this equation. Every resolution gives the same
  theta_C; taking two instances states independence without a cochain comparison map.
- `roof` is the requested equation for arbitrary C←q H→f J, with q a quasi-isomorphism.
  Lean writes composition left to right: localized_C ≫ inv(B_D(Qq)) ≫ B_D(Qf) equals
  inv(A_D(Qq)) ≫ A_D(Qf) ≫ localized_J. Transport along the representative
  factorization isomorphisms turns these maps into [B(q)], [B(f)], [A(q)], [A(f)].
  This is the TeX equation B(f)B(q)^(-1)theta_C = theta_J A(f)A(q)^(-1).
  The natural-isomorphism types additionally give naturality for every derived
  morphism, without a roof-choice hypothesis.
- There are no constructibility, boundedness, completeness, finite-presentation or
  discreteness hypotheses anywhere.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (reexports
  `Sheaf.NumberTheory.Padics.CoefficientExtension`):
  `Padic.coefficientExtensionIntegers`, with the recorded valuation-ring construction.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` (and its public imports):
  `completedIntegralCoefficientSheafUnrestricted`,
  `completedIntegralCommRingSheafUnrestricted`, the constant-to-completion cone.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  exactly Mathlib `SheafOfModules`, with Mathlib's abelian instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; `Mathlib.Algebra.Homology.QuasiIso`:
  `QuasiIso` (the mathlib leaf has no lean record, as permitted).
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, exactness of the actual sheafified tensor functor.
- `Sheaf.Paper.PointFiniteFreeSectionsTensor`:
  `PointFiniteFreeSectionsTensorData`, `point_finite_free_sections_tensor`,
  `pointFiniteFreeEvaluation`, `pointFiniteFreeModuleTensor`. Its public owning module
  `Sheaf.Paper.CompletedIntegralScalarData` reexports the actual
  `completedOrdinaryScalarExtension`, `completedOrdinaryScalarComplex`,
  `completedDerivedScalarExtension`, `completedScalarCounit` from
  `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`; the already published
  scalar functor/counit is the same derived-change-of-rings interface instantiated
  by `completedScalarChangeData`, rather than a second functor chosen here.
- Proof imports: `Sheaf.Paper.PointProEtaleSectionsExact`:
  `AlgebraicGeometry.ProEtale.point_proEtale_sections_exact`;
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`;
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryCompIso`;
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`;
  `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`:
  `Functor.leftDerived_from_resolvingClass`;
  `Mathlib.CategoryTheory.Localization.Predicate`: `Localization.liftNatIso`,
  `Localization.liftNatTrans`, `Localization.natTrans_ext`.

Searches (2026-10-21):

- `msearch.py ... leanfinder` query “Natural sections tensor comparison descends to
  unbounded derived categories with counit normalization and K flat resolutions”:
  8 hits, including `Functor.mapDerivedCategoryFactors[h]`, general derived-functor
  comparisons, and Tor. None states this point theorem or its normalization formulas.
- `msearch.py ... loogle` query
  `Localization.liftNatIso, Functor.mapDerivedCategoryFactors`: 0 hits (Loogle did
  not recognize the first unqualified identifier). The actual declarations were
  subsequently read directly in Mathlib's `Localization/Predicate.lean` and
  `DerivedCategory/ExactFunctor.lean`.
- `msearch.py ... grep 'liftNatIso|mapDerivedCategoryFactors|sections.*tensor'
  Algebra/Homology`: 11 hits, generic localization/factorization declarations.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item ID, sections/tensor derived comparisons, and the proposed names:
  no declaration exactly stating this item, and no clash for the new names.
  The existing `Sheaf.Paper.PointSectionsScalarExtension.pointDerivedSectionsTensor`
  was opened and read together with its coefficient comparison and ordinary-derived
  comparison. It has the site field, coefficient fields, and section-module universe
  tied to the same u (sections in u+1), and does not assert the present arbitrary-roof
  and all-resolution normalization equations. Its scalar extensions/counit are the
  same published constructions used here; it is not an exact existing match for this
  independent-universe node. No definition from that module is copied.

Edge cases checked before drafting and on final reading:

- E=L, including the identity inclusion: no strict-extension or positive-degree
  assumption occurs. The formula specializes to the unit scalar tensor comparison.
- Zero complex and arbitrary zero terms: all formulas are equations of categorical
  morphisms; no nonzero module, element, or cohomology hypothesis is used.
- Unbounded complexes and negative cohomological degrees: all indices are ℤ, with
  no truncation or boundedness restriction. Infinite-rank/nonconstructible sheaves
  are allowed.
- Identity resolution and non-surjective quasi-isomorphic resolutions: both are
  included. K-flatness and flat terms are required only in the resolution clause;
  comparison_counit itself applies to all complexes.
- Every roof q, including identity q, with arbitrary f: the formula uses only the
  isomorphism obtained by localizing q, never a chosen chain inverse or K-flatness of H.
- Independent site/coefficient and module-localization universes: no equality was
  added to make the APIs typecheck. All variables/universes are explicitly bound.

No statement correction, disputed statement, new DAG node or dependency repair is
needed. The original node is changed only in `lean`. The one postponed theorem has
its complete mathematical proof in its docstring, following the node's counit,
localization and roof calculation. All abbreviations have actual defining terms.

Validation: the prescribed server `scompile.py` checked the module in both sandbox
and library-module contexts cleanly. The dry-run and final delivery results are
recorded by the prescribed delivery wrapper.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
