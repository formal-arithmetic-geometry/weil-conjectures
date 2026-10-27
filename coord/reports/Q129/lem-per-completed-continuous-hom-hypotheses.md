## Worker report

Item: `lem-per-completed-continuous-hom-hypotheses`, group Q129, stage 2.
Module: `Sheaf.Paper.CompletedContinuousHomHypotheses`.
Main declaration: `AlgebraicGeometry.Scheme.completedContinuousHomHypotheses`.
The only postponed theorem is the item itself, with proof `sorry` and the five
source proof steps in its docstring. All helper definitions have real data.
No node statement, statement dependency, proof, or other pre-existing field changes.

Hypothesis and clause correspondence (all names below are in
`AlgebraicGeometry.Scheme` unless qualified):

- Prime l: `(l : ℕ) [Fact l.Prime]`. Finite extension E of Q_l:
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  The valuation ring is the published `PbcIntegralRing l E`, the canonical ULift
  of `Padic.coefficientExtensionIntegers l E`. Its recorded `pbcUniformizer l E`
  defines `pbcIntegralDatum l E`; no arbitrary alternative ring is supplied.
  This is the coefficient convention of the recorded realization dependency.
- Scheme and geometric assumptions: `(X : Scheme.{u}) [IsNoetherian X]`,
  `[Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]`, and
  `[Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]`.
  The two `Fact.out` arguments to `PbcIntegralCategory` recover exactly these
  hypotheses, without adding global, connectedness, or nonemptiness conditions.
- Site, completed coefficients and continuous coefficients: the existing
  `X.ProEt`, `ProEt.topology X`, `pbcAdicCompletion X (pbcIntegralDatum l E)`,
  and `integralCoefficientSheaf l X E`. Their positive quotient index n is the
  exponent n+1. The universe remains object u+1 and morphism u on the site.
- Normalized coefficient identification: `(R : RationalModuleRealization l E X)`
  supplies `R.integralIso` and its finite quotient, pointwise normalization and
  locally closed restriction compatibility. This uses the recorded dependency's
  interface for e, not a new or arbitrary ring isomorphism. The other data in R
  are the existing realization data accompanying this e, not new assumptions.
- Module and derived categories: `pbcModules` is the existing `ringedSiteModules`
  specialization; `PbcCompletedDerived` is its recorded `DerivedCategory`.
  The continuous category is `DerivedCategory (pbcModules X
  (integralCoefficientSheaf l X E))`. Cohomological bounds use the standard
  `DerivedCategory.IsGE` and `DerivedCategory.IsLE` from its cohomology t-structure.
- Full completed category: every K or L is in `PbcIntegralCategory l E X
  Fact.out Fact.out`, the published full subcategory on
  `PbcIsBoundedConstructibleComplete`, including all compatible etale origins.
  Neither a bare finite-stratification condition nor a cohomology-only surrogate
  replaces this predicate.
- Fixed restriction transport: `completedContinuousTransport l E X R` is
  literally `pbcDerivedRestrict R.integralIso.inv`. Its construction uses the
  existing exact restriction functor and the standard mapDerivedCategory.
- A-linearity and equivalence: fields `linear` and `equivalence` of
  `CompletedContinuousHomHypotheses`. On the continuous side the module action
  is explicitly built from the ring map `continuousIntegralSections`, which
  sends each a to the compatible family of constant functions a. The inherited
  source action is the published completed constant-section action. The ring
  ULift is the recorded universe convention, not a change of coefficients.
- Cohomological bounds: field `bounds` preserves and reflects both IsGE and
  IsLE, exactly as source proof step 2. Integer shifts: the actual
  `completedContinuousTransportShift` instance is the existing exact-derived
  CommShift instance, with its canonical `commShiftIso q` used in the maps.
- Coproducts: field `coproducts` transports any colimit cofan on an arbitrary
  small `I : Type (u+1)` to the cofan with legs `T.map (s.inj i)` and states
  that this is again colimiting. No countability restriction is imposed here.
- Integral membership after transport: field `integral` applies the full
  completion predicate to `(pbcDerivedRestrict R.integralIso.hom).obj
  (T.obj K.obj)`. This expresses the continuous integral category in the
  specified e-coordinates: transport back to the completed coefficient sheaf
  and use exactly its full three-clause predicate. In particular the compatible
  etale-origin condition is retained, not silently omitted.
- The Hom assertion: field `comparison` quantifies over every integral K,
  every `I : Type (u+1)` with `[Countable I]`, every derived family M with
  `(∃ n : ℤ, ∀ i, DerivedCategory.IsGE (M i) n)`, and every integer q.
  Arbitrary colimit cofans s and t give the two ambient coproducts and their
  actual injections. Their isomorphism c is required to satisfy
  `T.map (s.inj i) ≫ c.hom = t.inj i` for every i.
- Identification of the actual maps: the component linear equivalences φ and
  target linear equivalence ψ have the prescribed formulas
  `T.map f ≫ (T.commShiftIso q).hom.app (M i)` and
  `T.map f ≫ (T.commShiftIso q).hom.app s.pt ≫ (shiftFunctor _ q).map c.hom`.
  The next equation is exactly
  `ψ (f ≫ (s.inj i)[q]) = φ i f ≫ (t.inj i)[q]`.
  Since φ and ψ are linear, equality on every direct-sum generator identifies
  the full direct-sum comparison square. Both actual maps are written as
  `DirectSum.toModule` of `Linear.rightComp` by the shifted coprojections,
  and each is `Function.Bijective`: precisely an isomorphism of A-modules.
- Every integral L is bounded: field `bounded` gives `∃ a b : ℤ, a ≤ b ∧
  IsGE L.obj a ∧ IsLE L.obj b`. The IsGE witness gives bounded below too.
  Shift closure: field `shifts` gives the full completion predicate on L[q]
  for every q, with the same witness-sensitive category.
- There is no flatness or projectivity binder on cohomology, and no assertion
  of Hom continuity without the common lower-bound hypothesis.

Dependencies read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its underlying valuation ring,
  ideal, uniformizer and coefficient topology declarations in CoefficientExtension.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`,
  `Scheme.ProEt.topology`.
- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`,
  `pbcAdicCompletion`, and their existing positive quotient tower conventions.
- `Sheaf.Paper.ContinuousConstructibleModule`:
  `AlgebraicGeometry.ProEtale.IsContinuousConstructible` and the recorded
  continuous coefficient sheaf construction; no new constructibility predicate.
- `Sheaf.Paper.RationalModuleRealizationFunctor`:
  `RationalModuleRealization`, `rationalModuleRealizationFunctor`, and
  `integralCoefficientSheaf` from its published supporting imports.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`; standard IsGE/IsLE come from the
  public TStructure supporting imports of the realization interface.
- `Sheaf.Paper.IntegralUniformCoefficient`, including its recorded supporting
  module `Sheaf.Paper.BoundedConstructibleComplete`: the published
  `PbcIsBoundedConstructibleComplete`, `PbcBoundedConstructibleComplete`,
  `PbcIntegralCategory`, `PbcIntegralRing`, and `pbcIntegralDatum`.
  The E : Type u / ULift specialization is the one used by the realization
  and Hom-sums dependencies. It is not a copied category definition.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, through the published `pbcRestrict`
  and `pbcDerivedRestrict` interfaces in BoundedConstructibleTower.
- Plain proof imports: `Sheaf.Algebra.Homology.NormalizedRingIsoDerivedTransport`,
  `Sheaf.Paper.IntegralConstructibleHomSums` (integralConstructible_hom_sums),
  and `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
  (integralStratifiedPerfectCharacterization and its shift-closure assertion).

Sources: read the actual local PDF around pp. 58–61 using pdftotext.
Lemma 6.8.2(1) identifies the inverse limit with continuous functions;
Proposition 6.8.11(3) characterizes integral constructible complexes by bounded
constructible cohomology; Lemma 6.8.12 supplies the common-lower-bound sum assertion.
The retained node proof supplies the explicit scalar and naturality calculations.

Edge cases checked before finalizing:

- I empty is allowed: no `[Nonempty I]`. The common bound is vacuous, both
  coproducts are zero, and both direct-sum and target Hom modules are zero.
  φ's family and the generator equation are vacuous, not an excluded case.
- Singleton I: the formula reduces to the actual shifted injection and the
  same normalized transport on arrows; it cannot be replaced by an unrelated
  bijection merely having the same endpoints.
- K=0 and empty X: no nonzero-object or point-existence binder is present.
- All positive and negative q are allowed, including q=0. Bounds a,b,n are ℤ.
- Torsion finitely presented A/varpi cohomology is allowed: neither flatness
  nor projectivity is required of K, L, or their cohomology.
- Arbitrarily unbounded-above M_i are allowed with a common lower bound.
  Families with no common lower bound do not satisfy the continuity premise.
- The site universes are not equated. The family index lives in the recorded
  small coefficient/site object universe u+1, as in the existing Hom-sums theorem.

Searches for an existing statement / definitions (actually run through msearch.py):

- LeanFinder: “Restriction of scalars along the completed continuous coefficient
  isomorphism preserves bounded constructible complexes and identifies countable
  bounded below shifted Hom coproduct comparisons”. Eight hits, all ordinary
  complex-restriction interfaces: HomologicalComplex.restrictionXIso.hcongr_13,
  HomologicalComplex.restriction.sc'Iso, its hom_τ₁ lemma,
  ComplexShape.Embedding.homRestrict_precomp, HomologicalComplex.restrictionXIso,
  HomologicalComplex.restrictionMap_f', CochainComplex.ConnectData.restrictionLEIso,
  and ComplexShape.Embedding.homRestrict.f_eq. No exact match.
- Loogle: `SheafOfModules.restrictScalars, DerivedCategory`: zero hits.
- Mathlib grep: `completedContinuous|continuousIntegralSections|constructible.*hom.*sums`:
  zero hits.
- LeanSearch: “Exact derived restriction along a normalized coefficient ring
  sheaf isomorphism preserves constructible complexes and identifies shifted Hom
  direct sum comparison maps”. Eight hits: LocallyRingedSpace.IsOpenImmersion.isoRestrict,
  HomologicalComplex.restrictionOpcyclesIso.congr_simp,
  LocallyRingedSpace.restrictTopIso, HomologicalComplex.restriction.sc'Iso,
  SheafedSpace.restrictTopIso,
  HomologicalComplex.pOpcycles_restrictionOpcyclesIso_hom,
  CochainComplex.ConnectData.restrictionGEIso,
  HomologicalComplex.restriction.congr_simp. No exact match.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for coefficient transport,
  constructible Hom sums, and the new declaration names; exact-node grep in
  WeilConjectures. Existing generic exact restriction and shifted Hom-sums
  declarations were found and reused. ContinuousModuleEncodingUniverses defines
  a different ordinary internal-module/section-action encoding; it does not
  state this derived coefficient/Hom assertion. No new public declaration name
  conflicts with Mathlib, WeilConjectures, Sheaf, or dag/lean_names_upstream.json.

No STATEMENT-DISPUTED issue or statement correction. No new independent notion
or dependency repair is needed. The constant scalar ring hom, its induced
linear structures, the exact derived transport abbreviation, its shift instance,
and the conclusion record are helpers of this single assertion and are all
listed in lean.declarations.

Validation: scompile.py compiled both the sandbox-renamed module and its library
module cleanly, without errors or warnings (5.7 s and 5.5 s in the final direct run).
An initial global `open Classical` style warning was repaired by declaration-local
`open Classical in`; no warning suppression or extra decidability hypothesis.

## Second reading by Q129

The dispatcher explicitly prohibits starting another agent. This is a separate
self-audit with both the node and final file open, not a claim of an independent
worker review; the maintainer's independent delivery review remains required.

Rechecked all geometric and coefficient binders against the node and the
recorded realization interface: prime, finite extension, noetherianity, finite
dimension, stalkwise l-invertibility and the normalized integralIso are present.
Checked the direction of restriction: e.inv has source A_X and target B_X, so
restriction sends B_X-modules to A_X-modules, as required. Its inverse coordinate
restriction uses e.hom, so `integral` is typed over the original B_X with the
complete recorded witness predicate. Checked the category membership is not
replaced by only boundedness or stratum models.

Opened the comparison field against proof step 5: φ uses the shift isomorphism
at M_i, ψ uses the shift isomorphism at s.pt and then c[q]. The normalization of
c has T(iota_i) followed by c equal to j_i. Thus the generator equation has the
correct composition order and endpoints. Both DirectSum.toModule expressions
use exactly the corresponding shifted injections, not arbitrary module maps.
φ and ψ are linear equivalences, not merely bijections of underlying sets.
The generator equality suffices by the direct-sum universal property. Checked
that the target is Hom(TK,(coproduct TM_i)[q]), not Hom(TK,coproduct(TM_i[q]))
without a comparison. The s and t colimit premises provide arbitrary realizations
of the two displayed coproducts, rather than extra restrictions on the family.

Rechecked the remaining clauses: bounds are preserved/reflected; all small
coproducts are preserved independently of the countable continuity clause;
canonical integer-shift compatibility is already constructed from the exact
derived functor; every integral object has an integer interval of cohomological
bounds and every integer shift is in the full category. Empty/singleton families,
zero objects, empty schemes, negative shifts, torsion cohomology and a common
lower bound without any upper bound are all retained. The only change during
this final audit was replacing the globally opened Classical scope by the
local scope to satisfy the compiler's style check; no mathematical clause changed.
