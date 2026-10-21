## Worker report

The module `Sheaf.AlgebraicGeometry.FinitePullbackLocalizationCohomology` states
`AlgebraicGeometry.Scheme.finite_pullback_localization_cohomology`, with `sorry` as
its entire proof. Its helper structure `ProEtaleFiniteLocalizationComparison`
packages exactly the comparison data and equations of the same node. It constructs
no new pullback, restriction, cohomology, coefficient ring, or derived category.
No data definition contains `sorry`; there is one postponed theorem.

Hypotheses and clauses:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension E/Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The valuation ring and chosen uniformizer are the
  existing `Padic.coefficientExtensionIntegers` and
  `Padic.coefficientExtensionUniformizer` used in `coefficientExtensionRing`.
- Positive integer coefficient level: `(n : ℕ)` with quotient exponent `n + 1`.
  This reindexes every level at least one, with original level one at index zero;
  the zero coefficient level is not substituted for the first positive level.
- A = O_E/(varpi_E^(n+1)): exactly
  `Padic.coefficientExtensionRing l E (n + 1)`. The helper's `finite` evidence
  follows from the recorded `Padic.finite_coefficientExtensionRing`; it is
  part of the conclusion, not an additional assumption of the theorem.
- X and the site object u: `(X : Scheme.{u}) (U : X.ProEt)`; its domain scheme is
  `U.left`, its morphism is `U.hom`, and `U.prop` is weak etaleness. This quantifies
  over arbitrary site objects, including nonmonomorphisms.
- Ell invertible on both schemes: the two explicit instance binders
  `∀ x : X, Invertible (l : X.residueField x)` and
  `∀ x : U.left, Invertible (l : U.left.residueField x)`.
- Site and constant-coefficient identifications: `ringIso` compares the actual
  constant commutative ring sheaf on U with restriction by composition; its
  `constantSections` equation precomposes with the two actual sheafification units.
  Thus it is the unique identification fixing every constant section. Composition
  is the inverse direction of the recorded `ProEt.sliceEquiv`; its underlying
  functor is `MorphismProperty.Over.map (f := U.hom) ⊤ U.prop`.
- R_U is the existing `proEtaleObjectModuleRestriction U A ringIso`. Its definition
  is sectionwise module pushforward along composition, so its sections and morphisms
  are exactly F(V -> U -> X) with action restricted along `ringIso.hom`.
  `restrictionAdditive`, `restrictionLimits`, and `restrictionColimits` retain its
  exactness, without asking the theorem's user to assume it.
- L u*: `sfIntrinsicDerivedPullback A U.hom` is the recorded exact termwise
  intrinsic finite pullback. At the coefficient ring of this theorem it is
  definitionally `WeilConjectures.finiteDerivedPullback l E n U.hom`.
  `sfIntrinsicConstantModuleAdjunction` identifies its underived functor with the
  module pullback specified by `proEtaleCoefficientInverseImageMap`, preserving
  the actual constant-section scalar map. It is not an arbitrary supplied functor.
- Graph normalization: `moduleComparison` is an isomorphism of the actual module
  functors. `module_graph` fixes its inverse on every section x, at every module M
  and every V over U: apply the normalized module adjunction unit at V composed
  with U, and restrict along `proEtaleObjectInverseImageIndexPoint U V`.
  That index point is exactly the graph, defined by the composition/base-change
  adjunction unit. This is the graph coprojection followed by module
  sheafification and scalar extension, with the scalar-unit tensor 1 ⊗ x.
  It also fixes the comparison on module maps, because `moduleComparison` is a
  natural isomorphism, not a family of arbitrary object isomorphisms.
- Eta: `derivedComparison` has precisely the type Lu* ≅ D(R_U), using
  `R_U.mapDerivedCategory`. `derived_on_complexes` is its equation at every Q(K):
  eta_QK followed by the R_U localization factor equals the pullback localization
  factor followed by Q of the degreewise moduleComparison. This retains the
  exact representative normalization of the node.
- Cohomology is sheaf cohomology objects: both functors are
  `DerivedCategory.homologyFunctor (proEtaleRingModules ...) r`; this is ordinary
  cochain cohomology in the abelian module-sheaf category, not cohomology of the
  evaluated groups of sections. Every `r : ℤ` is included.
- c^r: `cohomologyComparison r` is the requested natural isomorphism, of type
  Lu* followed by H^r on U ≅ H^r on X followed by R_U.
- Cycles/boundaries normalization: `cohomology_formula` identifies it with
  cohomology of eta followed by the inverse of
  `R_U.mapDerivedCategoryHomologyFunctorIso r`. The latter's definition in
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` descends
  `mapHomologicalComplexHomologyIso`. Its definition in
  `WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso` is the short-complex
  canonical `homologyFunctorIso`, whose component is `ShortComplex.mapHomologyIso`.
  That is built from the preserved kernel/cokernel homology data, hence uses exactly
  the canonical cycle inclusion and cycle-to-cohomology projection. The upstream
  lemma `mapDerivedCategoryHomologyFunctorIso_hom_app_Q` displays its representative
  formula including both H^r factorization isomorphisms. No independent or
  unnormalized cohomology identification is introduced.
- All derived morphisms: `cohomology_naturality` quantifies over K,L in the
  ordinary unbounded `proEtaleDerivedCategory X A` and every `ψ : K ⟶ L`.
  In Lean's left-to-right composition it reads H^r(Lu*ψ) ≫ c_L =
  c_K ≫ R_U(H^rψ), exactly the displayed right-to-left equation of the node.
  Roofs are included because ψ is a derived morphism without any representative
  assumption. No boundedness, constructibility, surjectivity, or open-immersion
  hypothesis is imposed on the input complex or site object.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its imported coefficient constructions
  in `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`, read for its exact coefficient and
  ambient-category conventions; the theorem does not restrict to that subcategory.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `ProEt.weaklyEtale_localization`, `sliceEquiv`, `sliceFrom`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `over`, `overMap`, `overFunctorMap`, and
  `pushforward`, which implements `proEtaleObjectModuleRestriction`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `SheafOfModules.localizedSystemRestriction`, `localizedSystemExact` and its
  additive/finite-limit/finite-colimit projections, read for the exact slice
  restriction used in the proof plan.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, `HasDerivedCategory.standard`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `WeilConjectures.finiteDerivedPullback`,
  and its underived/derived functors from `ProEtaleIntrinsicFiniteOperations`,
  `sfIntrinsicPullback`, `sfIntrinsicDerivedPullback`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `proEtaleSheafInverseImage`, `proEtaleCoefficientInverseImageMap`,
  `proEtaleConstantRing`, `proEtaleConstantModulePullback`, and its morphism map.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicConstantModuleAdjunction`, the actual normalized adjunction used in
  the graph equation. The tensor-unit-normalized ring-module adjunction is in
  `ProEtaleOperationsCanonicalAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`:
  `proEtaleObjectInverseImageRestriction`, `proEtaleObjectModuleRestriction`,
  `proEtaleObjectInverseImageIndexPoint` and `ProEtaleObjectRestrictionComparison`.
- Repaired cohomology record: `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
  defines `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`. The standard
  t-structure in the node is the existing `DerivedCategory.TStructure.t` in the
  Mathlib `TStructure` module; the consumer only uses cohomology.
- Proof inputs: `Functor.mapDerivedCategoryFactors` (Mathlib ExactFunctor),
  `Functor.exactFunctor_derivedFunctor` (Sheaf ExactFunctorDerivedFunctor),
  `proEtaleConstantRingDerivedPullback` (ProEtaleConstantRingOperations),
  `Localization.liftNatIso`, `liftNatTrans`, `natTrans_ext` (Mathlib Predicate),
  and `Functor.homologyFunctorIso` / `ShortComplex.mapHomologyIso`
  (Mathlib ShortComplex/PreservesHomology). The upstream exact-derived-functor
  module supplies the fully normalized derived and cohomology comparison APIs.

Edge cases checked before writing: U empty; X empty; u = identity; u nonmono
(e.g. a disjoint union of two copies); original coefficient level one; E = Q_l;
nonfield quotient coefficients; zero and acyclic complexes; arbitrary negative and
positive cohomology degrees; complexes unbounded in both directions; arbitrary
roofs. None is excluded. The site keeps object universe u+1 and morphism universe u;
module coefficients and sections have the existing u+1 lift. No extra equality of
site universes, geometric-stalk conservativity, or finiteness of the scheme is used.

Searches (2026-10-21):

1. msearch leanfinder, query "Derived pullback along an object of the small pro
   etale site is naturally isomorphic to exact slice restriction and commutes with
   cohomology with its graph normalization": eight generic module pullback hits,
   including `SheafOfModules.pullbackObjFreeIso` and `pullbackIso`; no exact match.
2. msearch loogle, query
   `CategoryTheory.Functor.mapDerivedCategory, CategoryTheory.Functor.homologyFunctorIso`:
   zero hits, unknown identifier for homologyFunctorIso in the search index.
   Direct source reading located the existing generic exact-functor comparisons;
   they are reused, not restated as new theorems.
3. msearch grep, query
   `proEtale.*[Rr]estriction|mapDerivedCategory.*[Hh]omology`: zero indexed hits.
4. msearch leansearch, query "Derived pullback along a pro etale site object is
   the exact module restriction to the slice site and commutes with cohomology
   naturally with graph normalization": eight generic sheaf pullback and scheme
   restriction hits, none the specified pro-etale derived comparison.
5. rg of Mathlib for exact-derived-factorization, localization lifting,
   mapHomologyIso, and homologyFunctor: found the generic APIs cited above.
6. rg of project `lean/WeilConjectures` and `lean/Sheaf`, including the exact item
   id and proposed declaration names: no declaration for this node and no name
   collision. Source `mapDerivedCategoryHomologyFunctorIso` is generic, and
   `proEtaleObjectInverseImageRestriction` is underived. The separately read
   `ProEtaleDerivedOpenRestriction` concerns open base change of direct image,
   not the present normalized pullback/cohomology comparison for any site object.

The local Stacks source was opened at sites.tex lemma-localize-given-products,
homology.tex lemma-exact-functor, and derived.tex lemma-right-derived-exact-functor.
These give the site adjunction, exactness criterion, and unbounded representative
computation. No source statement correction is needed. No STATEMENT-DISPUTED fault.
The repository's example CompactObject module is withdrawn and contains no remaining
example declarations; its node now records existing Mathlib compactness.

## Dependency modules

`def-weil-derived-cohomology-sheaves`: lean-only §1(B) repair to the exact existing
Mathlib declarations, with `existing: true`. Its recorded `sfModelCohomology` applies
to specialized intrinsic common-stage Weil categories with global field and model
data, whereas this dependency's current statement is ordinary cohomology of modules
on any ringed site. `DerivedCategory.homologyFunctor` and `homologyFunctorFactors` give that
ordinary cohomology and its representative normalization literally. The standard
t-structure clause uses the existing Mathlib `DerivedCategory.TStructure.t`. This avoids defining any new cohomology functor. Only
that dependency's `lean` field changes; there is no additional Lean module.

## Second reading by Q109

Final self-audit with the node and the file open; no separate agent was started,
as required by the dispatcher brief. Independent review is the maintainer's review
of this delivery. The audit matched every hypothesis and clause as listed above.
The positive-level reindexing includes original n=1. The graph equation fixes the
inverse module comparison on every section, and its adjunction uses the actual
scalar-unit normalization. The derived equation has the factorization arrows in
Mathlib's left-to-right order. The cohomology isomorphism is the inverse of the
upstream H^r-commutation iso after cohomology of eta, so its direction is correct.
The naturality quantifier ranges over all derived arrows, not only Q of chain maps.
The only interface mismatch found was the specialized cohomology dependency record;
it was repaired to the generic existing Mathlib declarations, without changing the
node's mathematical statement. A missing namespace qualification on
`Functor.isoWhiskerRight` found by compilation was fixed.

Validation: `scompile.py Q109 lem-pur-finite-pullback-localization-cohomology`
passed both the sandbox and actual-module passes, in 33.2 s and 25.5 s, with no
errors or warnings. The earlier expensive elaboration was repaired with the
standard transparency settings and by disabling unnecessary generated SizeOf,
constructor-index and injectivity declarations for the comparison structure.
The per-file limit remained 60 s. All Lean lines are at most 100 characters;
autoImplicit is disabled. The item and dependency copies differ from the read
repository only in `lean`.

Dry-run repair: the existing-declaration preflight requires the module defining
the declaration itself. The cohomology record initially named the reexporting
TStructure module; it now names HomologySequence, where homologyFunctor and
homologyFunctorFactors are defined. The consumer imports that exact module.
