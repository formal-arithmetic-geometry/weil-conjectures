## Worker report

The delivery states `AlgebraicGeometry.ProEtale.openProEtaleCounitScalar` in
`Sheaf.Paper.OpenProEtaleCounitScalar`, with its site-compatibility clauses in
`openProEtaleCounitScalar_site` and `openProEtaleCounitScalar_transport`.
All three theorem bodies are `sorry`. Four helper definitions have real data and
belong to this node's maps; no new mathematical notion or DAG node is introduced.
The existing node is unchanged except for `lean`.

Read the current item, all statement dependencies and their recorded declarations,
the resolved stage-1 re-split repair note, and the source Locality paragraph of
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`.
The repair note is resolved, not an outstanding stage-2 return. Its current accepted
assembly proof is retained and reproduced step by step in the main theorem docstring.

Hypothesis and conclusion correspondence:

- The prime is `ell` with `[Fact ell.Prime]`. The field is `k : Type u` with
  `[Field k] [CharP k p]`, `_hp : 0 < p`, `_hEll : p ≠ ell`.
- `A B : Type u`, `[CommRing A] [CommRing B] [Finite A] [Finite B]` and
  `φ : A →+* B` are exactly the finite commutative coefficient rings and unital map.
  The common exponent is `n : ℕ` with `_hA : (ell ^ n : A) = 0` and the same for B.
  Since ell is prime, N = ell^n is automatically at least one; n=0 is allowed and
  forces both rings to be zero rings. No flatness or projective-dimension binder occurs.
- `U X : Scheme.{u}` and their `Over (Spec (.of k))` instances introduce the schemes
  and structure maps. `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` on
  each structure map are separated finite type over k. `[j.IsOver ...]` is the
  k-morphism condition, `[IsOpenImmersion j] [QuasiCompact j]` is the specified qc open.
- `M` is an ordinary unbounded derived fixed-coefficient module-sheaf object on
  `Scheme.ProEt.topology X`. The canonical `ULift.{u+1,u}` presents the small finite
  ring in the module universe required by the original small pro-etale site.
  The site's object universe remains u+1 and its morphism universe remains u.
- `_hBounded` is the standard t-structure boundedness predicate.
  `_hConstructible` tests every actual homology sheaf with the dependency's
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`, whose finite positive stratification,
  constructible locally closed strata, local constancy and finite geometric stalks
  are intrinsic, not an assumed etale origin.
  `_hTor` uses `Scheme.HasFixedCoefficientProEtaleTorAmplitude` for one ordered
  interval and every degree-zero module sheaf, exactly the recorded dependency.
- `liftedScalarExtension φ T` is the existing ordinary derived coefficient extension.
  Its `scalarPresentation` is the canonical realization comparison to the recorded
  `scalarExtensionFunctor`, preserving the underlying scalar adjunction and tensor unit.
- `openCounitScalarMap φ j` is b_j. It uses `proEtaleCoefficientMap φ
  (Compactification.ofIsOpenImmersion j)`, which is definitionally the genuine
  `transportedRecordedReductionDirectImageComparison` of the recorded intrinsic
  `reductionDirectImageComparison`. It removes the identity proper factor by
  `rightDerivedLowerStarId`, whiskering on both boundaries. Thus it cannot ignore
  or replace the named b with a freely chosen tensor isomorphism.
- `openCounitRestrictionScalarIso φ j` is a_j. It conjugates the inverse of the
  existing `scalarPullbackProEtaleIso (uliftRingHom φ) j` by the actual derived
  pullback/exact restriction identifications. This scalar isomorphism is the
  inverse restriction/scalar adjunction mate, normalized by K-flat balancing,
  i.e. the fixed-module presentation of `directImageScalarPullbackIso` inverse.
- `unboundedOpenProEtaleAdjunction` is the actual degreewise summand evaluation
  adjunction localized on the unbounded derived categories; no adjunction is an input.
  Its full finite-Tor subcategories have exactly the same Hom sets and counit.
- `∃ e, e.hom = b_j(U_A M)` asserts invertibility of the particular component of b_j,
  retaining its morphism. The next conjunct is exactly, in Lean composition order,
  `b_j(U_A M) ≫ J_B.map (a_j.app M) ≫ v_B.app (T_X M) = T_X.map (v_A.app M)`.
- The final conjunct transposes `e.inv ≫ T_X.map(v_A.app M)` under the actual
  B-open adjunction, and equates it to a_j. This is the component of the right mate
  of b_j inverse; naturality is inherited from the named natural transformations.
- `_site` is the displayed coefficient/site square specialized to the open:
  `T_X(e_A(L)) ≫ b_j(C_U L) ≫ J_B(delta_U(L)) =
  delta_X(J_A^e L) ≫ C_X(beta_j(L)) ≫ e_B(T_U^e L)`.
  Here beta is the existing `Etale.properOpenCoefficientOpenIso` normalized
  summandwise on K-flat representatives, and delta is `pbcComparisonReduction`.
- `_transport` gives the actual counit equation, the actual adjunction Hom-bijection
  equation, and its identification with `fixedCompactSupportComparisonIso` for
  the identity proper factor. It is quantified over the finite-Tor etale inputs
  and hence states the advertised transport including the counit. Common-refinement
  compatibility is the already recorded
  `etaleProEtaleCoefficientCompatibility_refinement`: its siteRefinement is composed
  from these fixed site comparisons and the canonical compactification comparison.
  Substituting `_site` at the identity factor and that refinement square gives the
  same b_j for any common refinement; no new comparison is selected.
- The Tate-line paragraph fixes the coefficient convention but no twist appears in
  this node's equation. The recorded `finiteEtaleTateTwist` module is imported and
  retained; there is no extraneous degree or twist hypothesis.

Dependency declarations used (modules and names):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField`; its standing geometry is rendered by
  the explicit binders, not by specializing to a chosen condensed coefficient.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the existing derived module
  categories and homology functor, not another localization.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`:
  `Scheme.HasFixedCoefficientProEtaleTorAmplitude`.
- `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`:
  `AdjunctionTransfer.etaleProperty`, with the recorded finite-Tor equivalences.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `scalarExtensionFunctor`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: the existing ordinary
  coefficient extension interface, retained as a statement-dependency import.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`: `Scheme.finiteEtaleTateTwist`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicExtensionByZero`, used by the recorded intrinsic b and its
  canonical `sfIntrinsicModuleEquivalence` realization in the fixed presentation.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: canonical constant inverse image;
  the fixed `upperStarIsoOpenImmersionRestriction` gives its open coordinates.
- `Sheaf.Paper.MateOpenRestriction`: `CondensedRing.mateOpenImmersion`; its
  counit-preserving open normalization is retained as a dependency import.
- `Sheaf.SecSmoothPurity.ReductionDirectImage` and its definition module:
  `reductionDirectImageComparison`, `reductionDirectImage_isIso`.
- `Sheaf.SecSmoothPurity.DirectImageScalarOperations`:
  `directImageScalarPullbackIso`, represented by the existing fixed scalar mate.
- `Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction`:
  `fixedCompactSupportComparisonIso`.
- `Sheaf.AlgebraicGeometry.UnboundedOpenCounitSiteTransport`: the actual
  `unboundedOpenEtaleAdjunction`, `unboundedOpenProEtaleAdjunction`,
  `unboundedOpenExtensionComparison`, `unboundedOpenRestrictionComparison`, and
  `unboundedOpenCounitSiteTransport` (ordinary proof-only import would hide the
  actual data needed by the signature, so this module is a public import).
- `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`: the named
  `CoefficientCompatibility.proEtaleCoefficientMap` and its genuine transport;
  site/refinement/sum compatibility theorems are the proof's plan.
- `Sheaf.Paper.EtaleProEtaleScalarMate`: `scalarPullbackProEtaleIso`, with
  `openCounitRestrictionModel` expressing it using exact restriction.
- `Sheaf.Paper.EtaleProEtaleScalarPullbackCube` is a proof-only import.
  `lem-sp-etale-open-counit-flat-models` has no recorded module yet, so there is
  none to import. Its proof step is retained verbatim in substance in the docstring.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv` and its counit formula;
  the statement spells the right-mate component with the actual Hom equivalence.

Edge cases checked before writing: identity open; empty open and empty scheme
(the degreewise evaluation on an empty sum is zero); zero M; zero coefficient ring;
n=0 (both rings zero); arbitrary nonflat map such as Z/ell² -> Z/ell. There is no
etale-origin assumption on M, no positive n restriction, no nonzero ring hypothesis,
no same-universe requirement on site objects and morphisms, and no arbitrary b or a.

Searches actually run through msearch.py with NV and the item id:

- LeanFinder: “The actual proetale open extension by zero counit commutes with derived
  scalar extension without flatness”: 8 results, including condensed solid counits,
  ordinary ModuleCat scalar counits, and differential lemmas; no geometric match.
- Loogle: `CategoryTheory.mateEquiv, CategoryTheory.Adjunction.counit`: 4 generic
  mate counit/app formulas, none states this coefficient/site comparison.
- LeanSearch: “Open extension by zero adjunction counit commutes with derived extension
  of coefficients”: 8 generic derived adjunction and module counit results, no match.
- grep: `open.*[Cc]ounit|[Cc]ounit.*[Ss]calar|mateEquiv`: 25 displayed hits in
  Mathlib, generic topology/module/mates formulas, no matching theorem.
- `rg` of WeilConjectures and Sheaf for the item id and open/counit/scalar names,
  followed by reading the existing normalization and coefficient transport modules.
  The item has no existing declaration. A final name search for all new names in
  Sheaf, WeilConjectures and dag/lean_names_upstream.json found no collision.

No statement correction or disputed statement. The only changes during compiler
iteration were parsing field accesses across line breaks and shortening long lines.
The three theorems remain statement-only. Compile uses scompile.py exclusively.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
