## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons`
states the exactness of actual-ring pro-etale module inverse image and the full
representative-normalized local comparison. Both theorem proofs are `sorry`:
`AlgebraicGeometry.Scheme.ProEtaleLocalRestriction.inverseImage_exact` and
`AlgebraicGeometry.Scheme.ProEtaleLocalRestriction.comparisons`.
All other declarations are transparent abbreviations, proof-instance projections,
or the explicitly constructed isomorphism `comparison`; none chooses unspecified data.
There is no statement correction and no disputed assertion.

Hypothesis and clause correspondence (namespace below is
`AlgebraicGeometry.Scheme.ProEtaleLocalRestriction`):

| Node text | Lean rendering |
| --- | --- |
| A morphism g : S → T of schemes | `{S T : Scheme.{u}} (g : S ⟶ T)` |
| R a sheaf of commutative rings on T_proet | `(R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})` |
| U any object of S_proet | `(U : S.ProEt)`; no immersion predicate |
| Actual ring R' = g⁻¹R | `inverseRing g R` is `ring ((proEtaleSheafInverseImage g CommRingCat).obj R)`, using the recorded inverse-image functor |
| R'_U | `(inverseRing g R).over U` on `(ProEt.topology S).over U` |
| F_g, without coefficient extension | The recorded `proEtaleModuleInverseImage g R`, unchanged |
| G_U, slice restriction | `restriction g R U` is exactly `SheafOfModules.overFunctor.{u+1} (inverseRing g R) U` |
| F_g and G_U exact | `inverseImage_exact` asserts additivity and preservation of finite limits and colimits for F; G's three instances are projections of the already-proved `ringedOverFunctor_exactGeneral` |
| Unbounded derived categories | Mathlib `DerivedCategory (SheafOfModules ...)`, with explicit `HasDerivedCategory.{wT}`, `.{wS}`, `.{wU}` binders; these specify localization sizes and impose no geometric or cohomological restrictions |
| DF_g and DG_U by exact localization | The two functors' `mapDerivedCategory` constructions |
| Choose C representing DF_g(K) | `DerivedCategory.Q.objPreimage ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj K)` |
| L(K) = Q_U(G_U C) | The `hobj` field of `comparisons` is equality with the recorded `ringedSiteDerivedRestrictionOfUniverses`, whose body is precisely this Q/termwise-restriction/representative formula |
| DG_U DF_g(K) ≅ L(K), with specified normalization | `α` is a natural isomorphism; `∀ K, α.app K ≪≫ eqToIso (hobj K) = comparison g R U K` fixes it to the explicit representative comparison |
| Comparison from epsilon and exact localization factor | `comparison` is DG applied to `(Q.objObjPreimageIso (DF.obj K)).symm`, followed by `G.mapDerivedCategoryFactors.app (Q.objPreimage (DF.obj K))` |
| Transport morphisms functorially | The map conjunct says `L.map a = α.inv.app K ≫ DG.map (DF.map a) ≫ α.hom.app K'`; L is a genuine functor, so identity and composition are included |
| Transport isomorphisms | L is a functor and α a natural isomorphism, hence applies to hom and inv and preserves their inverse identities; the displayed transport equation applies to both |
| Every q ∈ ℤ and natural G F H^q(K) ≅ H^q(L(K)) | `∀ q : ℤ, ∃ c : Hq ⋙ F ⋙ G ≅ L ⋙ Hq, ...` |
| Cohomology compatibility with α | The component equation fixes c to `G.map(h_F.hom.app K) ≫ h_G.hom.app (DF.obj K) ≫ Hq.map (α.hom.app K)` using the existing kernel/image-normalized `mapDerivedCategoryHomologyFunctorIso` |
| Every r ∈ ℤ, every R-module M, M[r] | `∀ r : ℤ`, with domain functor `DerivedCategory.singleFunctor ... 0 ⋙ shiftFunctor _ r`; its domain is all `SheafOfModules (ring R)` |
| Natural L(M[r]) ≅ (G F M)[r] | The natural isomorphism s has exactly these source and target functors |
| Shifted-single compatibility | Its component equation is α⁻¹, then DG(DF's commShiftIso), then DG's commShiftIso, then the shift of DG(single comparison for F) followed by the single comparison for G |
| Agreement of the two normalizations | Both component equations use the fixed exact-functor cohomology, single and signed-shift comparisons. These are the same representative-level kernel/image and degree-zero comparisons; no arbitrary cohomology or shift isomorphism is selected |
| No additional assumptions | There is no flatness, immersion, boundedness, Noetherianity, finite-type, coefficient-ring identification, or ring-completion binder |

The object and Hom universes of the original site remain u+1 and u, respectively;
the modules and coefficient rings have size u+1. The independent localization
morphism sizes wT, wS and wU are explicitly bound. No site universe is forced to
equal a localization universe. `autoImplicit` is false. Every variable and universe
is explicitly declared.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSheafInverseImage`,
  `proEtaleModuleInverseImage`; the latter is the specified small-model transport
  of module pullback along the actual adjunction unit, transported back, not
  pullback to an independently supplied ring.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, with `CategoryTheory.Sheaf.over` and the slice
  topology from `Mathlib.CategoryTheory.Sites.Over`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`; all types here use that same Mathlib category.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
* `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`,
  `Functor.mapDerivedCategorySingleFunctor`, and the canonical `CommShift` instance.
* `Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses`:
  `CategoryTheory.ringedSiteDerivedRestrictionOfUniverses`, the recorded representative
  construction, used verbatim as the object normalization.
* `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, the exact `mathlib_match` of
  `def-weil-derived-cohomology-sheaves`. That node's present primary declaration
  `sfModelCohomology` belongs to an unrelated common-stage model, so the general
  and explicitly recorded Mathlib match supplies this general-site cohomology.
* `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`:
  `CategoryTheory.ringedOverFunctor_exactGeneral`. Its already-landed owning node
  `def-weil-pbc-ringed-derived-restriction` is added to stmt_deps under brief-stage2 §5
  (STMT_DEPS MAY GAIN LANDED NODES). This supplies slice exactness without using
  the SmallCategory-only interface of `overFunctor_exact` on the unequal-size site.
* `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryHomologyFunctorIso`, read with its component formula
  on Q(K); this is the canonical descent of the kernel/image comparison.

The non-public imports preserve the node's proof plan: module inverse-image
comparison, site inverse-image exactness, the module forgetful functor and slice
restriction exactness. The remaining homology and factorization proof inputs are
in the public Mathlib/upstream import closures. There are no dependency repairs,
new nodes, or extra postponed lemmas.

Edge cases checked before writing and on the final statement:

* The empty source or target scheme and the zero coefficient ring require no
  nonempty/nonzero assumptions; the same inverse-image and slice formulas apply.
* The object U is arbitrary, including the empty object, and need not be an immersion.
* K ranges over the entire unbounded derived category, including the zero object.
* q is any integer, positive, zero or negative. r is independently any integer;
  the single complex is in degree zero and shifting by r concentrates it in degree -r.
* Identity g, arbitrary nonflat g, and rings differing from completed coefficient
  rings are all retained. The only coefficient ring on the source site is the
  actual inverse image of R.
* Functoriality is on all derived morphisms; no choice of a functorial complex
  representative is assumed. The conjugation formula defines the required maps.

Searches (2026-10-21; msearch output retained in searches.jsonl):

* `msearch.py ... leanfinder "Exact inverse image of module sheaves and derived
  slice restriction commute with cohomology and shifted degree zero complexes"`:
  eight hits, concerning pullback composition/free modules and scheme module
  restriction; none states the node's full comparison.
* `msearch.py ... loogle "CategoryTheory.Functor.mapDerivedCategoryFactors,
  DerivedCategory.homologyFunctor"`: zero hits.
* `msearch.py ... grep "mapDerivedCategory.*[Hh]omology|mapDerivedCategorySingleFunctor|objObjPreimageIso"
  Algebra/Homology`: eighteen hits, including the factorization/single API and
  localization representative isomorphisms, all reused.
* `rg -n "ProEtaleLocalRestriction|localDerivedRestriction|local_derived_restriction"`
  on project and upstream sources plus dag/lean_names_upstream.json: no match.
* `grep -rn "lem-weil-pbc-local-derived-restriction-comparisons" lean/WeilConjectures`:
  no match.
* Grep of derived restriction/comparison in `lean/Sheaf`, `lean/WeilConjectures`, and
  the advisory DAG nodes found `overFunctor_derivedRestrictionIso` in
  `Sheaf.Algebra.Homology.SitePerfectModelRestriction`. It covers only the G/object
  part, with the same inverse comparison formula; it does not state inverse-image
  exactness or either natural normalized cohomology/shift clause. The arbitrary-ring
  `proEtaleAllRingDerivedInverseImage` uses a different ring-valued inverse image;
  it is not silently substituted for the specified commutative-ring construction.
* Read Stacks `derived.tex`, `lemma-right-derived-exact-functor` (015F): exactness
  preserves acyclic complexes and quasi-isomorphisms, so every complex computes
  the unbounded derived functor. This is the source of the normalization used here.

Validation: compiled through scompile.py in both its sandbox and library module
names. The initial pass found only one line-width warning, corrected before the
final clean compile. The delivery dry run also compiles the final source.

## Second reading by O4

A second pass by this same worker read the node and module side by side. The
dispatcher explicitly forbids starting another agent; independent review is left
to the maintainer, as the brief states. This paragraph does not claim an independent
second worker.

The pass checked all rows of the clause correspondence above against the final
signature. In particular, alpha goes from DG DF(K) to the representative-normalized
L(K), while epsilon goes from Q(C) to DF(K), so epsilon is inverted. The transported
map is alpha_K inverse, then DG DF(a), then alpha_K' forward. The cohomology formula
has G(h_F) before h_G before H(alpha). The shifted-single formula starts with
alpha inverse and uses DF's shift inside DG before DG's shift. The shift functor
then applies to the composite of the two degree-zero single comparisons. Thus the
source and target of every composite agree. The hobj equality transports only
between the functor's chosen object and the recorded representative object, not
between coefficient rings. Natural isomorphisms c and s ensure naturality for
all K and M; no objectwise arbitrary isomorphisms replace that requirement.
No clause, edge case or geometric hypothesis mismatch was found. The one
formatting mismatch (a line over 100 characters) was repaired.
