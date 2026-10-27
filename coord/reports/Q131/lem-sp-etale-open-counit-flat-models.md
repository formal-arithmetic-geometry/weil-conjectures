## Worker report

The module `Sheaf.Paper.EtaleOpenCounitFlatModels` states
`AlgebraicGeometry.Etale.OpenCounitFlatModels.etaleOpenCounitFlatModels`.
Its one theorem has proof `sorry`. All auxiliary definitions contain actual
functor, adjunction, chain-map, or proposition data; none contains `sorry`.
The returned H2 dependency-record fault is repaired with three new definition
nodes pointing to existing plain declarations and the already landed
`def-pur-open-coefficient-normalizations`. No Lean declaration or mathematical
statement is changed; no dependency module is introduced.
The unchanged source is blueprint main-20261015,
`sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`,
Locality, together with Stacks Tag 0GL6 (`remark-Rf-lower-shriek-change-of-rings`).
The full eight-step DAG proof is carried in the theorem docstring.

Hypotheses, one by one:

- The prime is `(ell : ℕ) [Fact ell.Prime]`. Positive characteristic is
  `(p : ℕ) (_hp : 0 < p)` and `(k : Type u) [Field k] [CharP k p]`;
  `_hpell : p ≠ ell` gives the distinct primes (positivity plus the field
  characteristic forces p prime; no extra prime-characteristic assumption).
- The schemes are `U X : Scheme.{u}`, each with its `Over (Spec (.of k))`
  instance. `IsSeparated` on the structure maps is separatedness;
  `LocallyOfFiniteType` and `QuasiCompact` on each structure map are finite type.
- `j : U ⟶ X`, `j.IsOver (Spec (.of k))`, `IsOpenImmersion j`, and
  `QuasiCompact j` give exactly the specified quasi-compact open k-immersion.
- `A B : Type (u + 1)` with `CommRing` and `Finite` instances are finite
  commutative coefficient rings, in the project's ordinary-module convention.
  `_hA` and `_hB` say `∃ n, ∀ x, (ell ^ n) • x = 0`. This is equivalent to
  the usual `(ell ^ n : A) = 0`, by testing at 1 and multiplying by any x.
  `φ : A →+* B` is a unital ring map. There is no flatness, projective-dimension,
  Noetherian-instance, or coefficient/site comparison hypothesis.

Clauses, one by one:

- The full subcategories C are the *existing*
  `ProEtale.exceptionalTransportEtaleObjects A T` and
  `ProEtale.exceptionalTransportProEtaleObjects A T` (and with B). The first
  intersects recorded bounded constructibility with an existential finite
  Tor interval. The second uses bounded intrinsic constructible cohomology
  and the Tor test against all pro-etale module sheaves. It does not assume
  etale origin. A nonempty interval in the existential causes no loss: the
  zero object also has amplitude [0,0].
- `openDomains A j` and `openDomains B j` contain four preservation clauses:
  exact etale/pro-etale restriction and extension by zero on those domains.
  For each T in `[U, X]` they also assert every pro-etale object has etale
  origin, and an equivalence of the full subcategories whose composite with
  the inclusion is naturally isomorphic to the *specified* exact comparison.
  Thus the equivalence is the restriction of C, not an unrelated equivalence.
- The next universal clause asserts `IsIso (coefficientMap φ j L)` for every
  etale finite-Tor constructible L on U. The following T-clause asserts
  preservation by the etale `scalarExtension φ T` and the ordinary fixed-ring
  pro-etale `SupportedEtaleTensorOrigin.proFixedScalar φ T`.
- For each K in the etale X-domain and every Tor interval a,b, the theorem
  supplies an actual cochain complex P and `Nonempty (DerivedCategory.Q.obj P ≅ K)`.
  No assumption `a ≤ b` is added to this clause.
- `scalarSiteModels φ X a b P` uses the existing `modelProperties` for
  flatness (`exactFunctor _ _ (tensorRight (P.X q))`), vanishing terms
  outside [a,b] (`IsZero`), and K-flatness against arbitrary acyclic complexes.
  It separately asserts constructibility of each term. It asserts the same
  flatness, support and K-flatness for ordinary B-extension, site pullback,
  B-extension of site pullback, and site pullback of B-extension.
  The two `IsIso ...scalarExtensionRepresentative` clauses identify these
  localizations with actual derived scalars. Exact site comparison is computed
  by its canonical `mapDerivedCategoryFactors`.
- The identical predicate is asserted for the termwise restriction U P and
  extension J U P. Consequently all three complexes, their site pullbacks,
  and ordinary B-extensions have exactly the asserted bounded flat K-flat models.
  `operationModels` additionally records actual *derived-category* isomorphisms
  from Q(U P), Q(J U P), and their site pullbacks to the corresponding etale
  and pro-etale derived operations on K. These are not just cohomology isomorphisms.
- `evaluationComplexMap` is the actual sheaf open-adjunction counit in every
  degree, with the canonical composite-complex and identity-complex boundaries.
  The upstream adjunction is the extension-by-zero evaluation: the identity
  on supported extension summands and zero on empty ones. The two
  `evaluationModelEquation` clauses assert that its localization is the
  actual derived counit over A, and over B on the ordinary B-model.
- `coefficientMap` is the recorded
  `CoefficientCompatibility.etaleCoefficientMap φ (Compactification.ofIsOpenImmersion j)`
  conjugated by the canonical `rightDerivedLowerStarIdIso`. Thus beta is the
  specified identity-proper-factor map; its proper identity boundaries are
  retained, rather than replaced by an arbitrary isomorphism.
- `sheafCoefficientIso` is the canonical ordinary open/scalar adjunction
  comparison (its right comparison is restriction of scalars commuting with
  exact inverse image). `coefficientComplexMap` applies it degreewise.
  `coefficientModelEquation` equates localized chain maps with the specified
  beta, inserting the exact-localization and K-flat scalar representative arrows.
  `sheetEquation` spells out the summand formula: the pure tensor of the
  open-unit summand inclusion of x and b is carried to the same summand
  inclusion of x tensor b. `sheetMap` is built from the actual open unit and
  its restriction identification; no summand, scalar action, or map is assumed.
- The final equality uses `properOpenCoefficientPullbackIso φ j |>.inv.app K`
  as a_j. That existing definition is precisely `scalarPullbackIso` transported
  through `leftDerivedUpperStarIsoMapDerivedCategory` on both sides.
  The three maps on the left are beta at U K, J_B(a_j,K), and the actual B
  derived evaluation counit. The right is scalar extension applied to the
  actual A derived evaluation counit. Composition order in Lean is `≫`.
- Every variable and universe is explicitly bound; auto-implicit and relaxed
  auto-implicit binding are disabled. Ordinary small pro-etale sites retain
  object universe u+1 and morphism universe u; coefficients are Type(u+1),
  with the derived-category universe u+2. No universe equality is imposed.

Dependency declarations used (the following are the recorded owners or their
publicly imported equivalent ordinary fixed-module interfaces):

- `sk-def-sfb-dc-setting`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, `AlgebraicGeometry.ProEtale.FiniteCoefficientModules`.
- `def-weil-pbc-etale-constructible-sheaf`: `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.
- `def-weil-proetale-constructible-sheaf`: `Sheaf.Paper.ProEtaleFixedModuleConstructible`, `AlgebraicGeometry.Scheme.IsConstructibleProEtaleFixedModuleSheaf`.
- `def-weil-proetale-tor-amplitude`: `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`, `AlgebraicGeometry.Scheme.HasFixedCoefficientProEtaleTorAmplitude`.
- `def-weil-pbc-site-comparison-morphism`: `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `AlgebraicGeometry.Scheme.proEtaleSiteComparison`.
- `det-sp-scalar-extension-functor`: `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`, `AlgebraicGeometry.ProEtale.scalarExtensionFunctor`.
- `lem-pur-derived-change-of-rings`: `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, `ModuleCat.nonempty_ordinaryDerivedChangeOfRings`.
- `def-weil-pbc-extension-by-zero`: `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, `AlgebraicGeometry.Etale.openImmersionLowerShriek`.
- `def-weil-extension-by-zero`: `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`, `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`.
- `def-weil-proetale-inverse-image`: `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`.
- `def-pc-flat-sheaf-modules`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, `CochainComplex.IsKFlatIndependentCoefficients`.
- `lem-weil-pbc-extension-by-zero-adjunction`: `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, `AlgebraicGeometry.Etale.openImmersionLowerShriekUpperStarAdjunction`.
- `lem-sp-et-proet-coefficient-compatibility`: `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`, `AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility`.
- `def-pur-etale-scalar-pullback-iso`: `Sheaf.Paper.PurEtaleScalarMateProjection`, `AlgebraicGeometry.Etale.scalarPullbackIso`.
- `def-sp-constructible-finite-tor-domains`: `Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport`, `AlgebraicGeometry.ProEtale.exceptionalTransportEtaleObjects` and `AlgebraicGeometry.ProEtale.exceptionalTransportProEtaleObjects`.
- `def-sp-bounded-flat-model-properties`: `Sheaf.Paper.BoundedFlatCoefficientSiteSquare`, `AlgebraicGeometry.ProEtale.BoundedFlatCoefficientSiteSquare.modelProperties`.
- `def-sp-etale-scalar-pure-tensor`: `Sheaf.Paper.EtaleSumCoefficientComputation`, `AlgebraicGeometry.Etale.etaleScalarPureTensor`.
- `def-pur-open-coefficient-normalizations`: `Sheaf.Paper.ProperOpenCoefficientRefinement`, `AlgebraicGeometry.Etale.properOpenCoefficientPullbackIso`.

The setting's compactification declaration is not substituted for ordinary
constant-ring modules: its role here is only the field/scheme setting, which is
written in full. `FlatOnSite` exposes `exactFunctor`; its recorded note explicitly
permits the ordinary ModuleCat tensor-flatness specialization.
`KFlatIndependentCoefficients` exposes the ambient `MorphismProperty.kFlat`
used by the existing model predicate. Pro-etale fixed-module inverse image,
extension and scalar functors are the upstream fixed-module constructions
publicly underlying the intrinsic recorded presentations. The module also imports
the stated proof-dependency modules (constructible comparison, exact comparison,
Tor comparison, flat constructible models, the two coefficient/site squares,
pullback line models, compact-support Tor windows, pullback coherence,
pro-etale extension comparison, localized module exactness, open/sum adjunction
agreement, and independent cochain tensor).

Only stmt_deps and lean change in the copied item relative to current main.
The original 18 statement dependencies are retained in their original order.
The four extra theorem dependencies rejected at a742849d0084 are removed from
this saved packet and replaced by the four definition-node references listed
above. The proof and proof_deps are unchanged, so proof dependencies on these
same theorem modules remain available. Their public imports also remain because
the unchanged statement uses the plain definitions in them. This is the requested
worker repair, not a reviewer FIX of stmt_deps.

The saved packet first passed the requested dry run at a00f35ae3cb, but that
mechanical result does not resolve the independent H2 finding. This revision
repairs that finding explicitly. Each new node records existing:true, has no
lean.file, and owns only plain definitions with real data. No theorem-constructed
object or .choose is claimed. The exact signatures and docstrings were reread in
the current landed sources. There are no private copies of flatness, K-flatness,
constructibility, finite Tor amplitude, or scalar/site constructions.

Edge cases checked by reading the definitions and source:

- U empty: extension inputs and all supported summands are zero; the counit
  and both routes of the equation are zero. No nonempty-open hypothesis appears.
- j identity: the evaluation is the actual adjunction counit, and canonical
  identity proper boundaries in beta are explicit, not silently discarded.
- Zero K, zero coefficient rings, and powers ell^0 are allowed. In the last
  case the ring is zero, and the assertion reduces to zero modules.
- a>b: the universal Tor test against the unit forces K zero. The zero complex
  satisfies all support/model clauses, including the displayed a,b; no ordered
  interval hypothesis was introduced here.
- Nonflat coefficients such as Z/ell^2 → Z/ell are permitted. Ordinary tensor
  is applied to bounded flat input models, never to an assumed projective
  resolution of B. No finite Tor dimension of B over A is required.
- The sheet-index set can be empty. Formula sheetEquation covers supported
  generators and the actual additive counit handles the zero empty summand.

Searches performed before drafting (msearch log is searches.jsonl):

- LeanFinder: "Bounded flat constructible etale complexes extension by zero
  counit commutes with derived scalar extension" returned 8 generic scalar,
  condensed and adjunction hits, including ModuleCat.ExtendRestrictScalarsAdj.counit_app;
  none is this sheaf/model/compactification statement.
- Loogle: "CategoryTheory.Adjunction.counit, CategoryTheory.Functor.mapDerivedCategory"
  returned 0 hits.
- Mathlib grep: "counit.*[Ss]calar|[Ss]calar.*counit" under CategoryTheory
  returned 0 hits.
- LeanSearch: "Extension by zero and inverse image preserve bounded
  constructible finite Tor amplitude derived complexes" returned 8 generic
  exact-functor/homology/complex-extension hits; none is this statement.
- Project rg searches for the item id in lean/WeilConjectures and lean/Sheaf
  found no existing statement. Searches for counit, scalar, KFlat,
  modelProperties, exceptionalTransportEtaleObjects,
  properOpenCoefficientPullbackIso and etaleCoefficientMap located the shared
  declarations used above. The exact source signatures and docstrings were read.
  The related sum, proper/open and coefficient/site theorems lack the complete
  open-domain/model/evaluation assertion of this node, so none is an existing match.

No disputed mathematical statement or source fault was found. The intermediate
compile diagnostics (missing finite-ring binder, excessive unfolding and long
lines) were repaired. The final source is compiled only with the prescribed
scompile.py; no global build, direct live edit, or repository git command was used.


## New nodes

`def-sp-constructible-finite-tor-domains` records the two existing object predicates
in `Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport`. The etale predicate
is the infimum of recorded bounded constructibility and an existential ordered
Tor interval. The pro-etale predicate is bounded cohomology, intrinsic
constructibility of every cohomology sheaf, and an existential ordered Tor
interval. It asserts no equivalence or etale origin. Its source is the blueprint's
finite-Tor restriction and the Locality paragraph. LeanSearch and LeanFinder for
"Bounded constructible finite Tor amplitude objects on etale and proetale sites"
gave generic sheaf and t-structure results, not these two predicates. Mathlib grep
for their names returned zero; upstream rg returned zero; Sheaf rg located these
existing definitions. DAG and blueprint searches found no definition node owning
the conjunctions. The new node uses existing:true and cites the existing
constructibility and Tor definition nodes; no module is copied or changed.

`def-sp-bounded-flat-model-properties` records the existing modelProperties in
`Sheaf.Paper.BoundedFlatCoefficientSiteSquare`. Every term is tensor-flat,
every term outside [a,b] is zero, and the supplied complex is K-flat. It neither
chooses nor asserts existence of a model, and imposes no a<=b restriction. Its
source is Stacks 06YQ and 08G1 (bounded flat models in sites-cohomology.tex),
whose statements were reread. LeanSearch and LeanFinder for "Complex of module
sheaves with flat terms zero outside an interval and K flat" returned generic
flat modules, support, and K-injective statements; Mathlib grep modelProperties
returned zero. Upstream rg returned zero; Sheaf rg located the plain predicate;
DAG searches found only its theorem owner. This node records existing:true with
the exact signature, rather than adding the coefficient/site-square theorem to
stmt_deps. It cites the existing flatness, K-flatness and cochain definitions.

`def-sp-etale-scalar-pure-tensor` records etaleScalarPureTensor in
`Sheaf.Paper.EtaleSumCoefficientComputation`: the value is b times the actual
scalar-adjunction-unit section, read in the underlying B-module. It imposes no
finite-ring or flatness hypothesis and asserts no generator equation. Stacks
0GL6 and the blueprint Charts paragraph explain this tensor notation in the
coefficient calculation. LeanSearch and LeanFinder for "Pure tensor section of
scalar extension of etale module sheaves from the adjunction unit" gave ordinary
module scalar-unit and Kaehler-differential results, not this sheaf section.
Mathlib and upstream exact-name grep returned zero. Sheaf rg located this plain
def; DAG and blueprint searches found no definition-node owner. The already
landed def-sf-etale-sheaf-scalar-extension supplies the ordinary functor and
specified adjunction and is cited by the new node. The primary signature is
verbatim and existing:true; no duplicate definition is written.

For all three nodes the precise msearch JSON results are retained verbatim in
mathlib_searches, together with project/DAG grep results and the blueprint search.
The fourth rejected theorem reference is replaced by the already landed
`def-pur-open-coefficient-normalizations`, whose recorded declarations include
exactly properOpenCoefficientPullbackIso. No fourth new node is necessary.

## Second reading by Q131

This is a worker self-check under the dispatcher instruction not to start another
agent; the maintainer supplies the independent reading. The returned mathematical
review accepted all hypotheses and clauses. I retained the byte-identical Lean
module and rechecked the affected interfaces against their full declarations:
exceptionalTransportEtaleObjects/ProEtaleObjects are plain predicates, modelProperties
is a three-part conjunction, etaleScalarPureTensor is a section built from the
unit and scalar action, and properOpenCoefficientPullbackIso is the canonical
exactness transport of scalarPullbackIso. None is constructed by a theorem.

The node and theorem still agree on the prime/characteristic and finite-type
scheme setting, quasi-compact open j, finite torsion coefficients, and arbitrary
phi. openDomains records the same restrictions, extensions and comparison
pinned to nu*. The scalar models and operationModels retain the specified flat,
constructible, strict-support and K-flat complexes and actual derived isomorphisms.
The local sheet equation uses the unit-defined pure tensor from the new def node.
coefficientMap remains the compactification (j,id) beta with canonical identity
proper boundaries; the final equation uses the inverse of the exact-pullback
scalar comparison, followed in the stated order by the actual derived counit.
The previously reviewed empty-open, zero-object, a>b and nonflat-coefficient cases
remain available. The three new TeX statements introduce their own objects and
match their exact existing signatures, without importing theorems as notions.
No additional mathematical mismatch was found.
