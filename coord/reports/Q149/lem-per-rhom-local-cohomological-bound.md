## Worker report

The module `Sheaf.Algebra.Homology.LocalRHomCohomologicalBound` states
`CategoryTheory.LocalRHom.local_cohomological_bound`; its sole theorem has proof `sorry`.
All other declarations are transparent abbreviations or concrete canonical maps. No new
DAG node, dependency repair, or statement correction is required.

### Hypotheses and clauses

* The ringed site is `{C : Type uC} [Category.{vC} C]`,
  `J : GrothendieckTopology C`, `R : Sheaf J CommRingCat.{max uC vC u}`.
  Site objects, site morphisms and the additional coefficient universe are
  independent, exactly as in the reviewed citer. `HasSheafify` and
  `WEqualsLocallyBijective` on the site and slices use `max uC vC u`;
  these are the sheafification size interfaces, not finiteness conditions.
  `Mod J R` is the recorded `ringedSiteModules`/`SheafOfModules` category,
  and `D J R` uses `HasDerivedCategory.{w}`. The slice categories have
  independent `HasDerivedCategory.{wSlice}` structures. Neither derived
  universe is identified with any site or coefficient universe. All universe
  variables and term variables are explicitly bound (`autoImplicit false`).
* Fixing `K : D J R`, `RH J R K` curries the recorded
  `derivedInternalHomOfUniverses.{uC, vC, u, w}`; `T J R K n` composes it with
  `DerivedCategory.homologyFunctor _ n`. This is precisely the stated T^n.
* Clause 1: `P n : D J R ⥤ PresheafOfModules` is the local derived Hom module
  presheaf, specified by additive bijections `e n M U`. Its scalar equation is
  postcomposition with `sectionDerivedMultiplication.{uC, vC, u, w, wSlice} J R U a`; its restriction
  equation is `restrictHom`, conjugating the derived `overMap` by `resComp`.
  Its map in M is postcomposition with derived restriction of `v[n]`.
  `σ n : P n ⋙ sh J R ≅ T J R K n` is a natural isomorphism of module sheaves,
  hence linear and additive and compatible with sheaf restriction.
  The final representative clause uses every source representative `L` with
  `k : Q L ≅ K` and every K-injective `I`. The equation for `h` normalizes its
  comparison to the existing fixed K-injective augmentation and localization
  factorization. For every local cocycle `z`, the chain map `a` has precisely the
  `homComplexπ` components of z. The equation through `cycleClass`, `σ.inv`, the
  sheafification adjunction unit, and `localizedCocycle` says its class is exactly
  the local derived morphism, including the source representative and shift
  comparisons. Arbitrary M is covered by its K-injective representative.
* Clause 2: `(T ... n).Additive` for every integer n and `(T ... 0).IsHomological`
  are explicit. `S` is a `ShiftSequence` with `τ n : S.sequence n ≅ T ... n` and
  `τ 0 = S.isoZero`. Its zero/addition coherence supplies all shift comparisons.
  The canonical boundary is `boundary J R K S τ A n`. For every distinguished
  triangle and every n, the presheaf map `d` is specified on all local sections
  by postcomposition with `w[n]`, followed by the canonical shift-addition map.
  Its sheafification is identified with that boundary via σ. Mathlib
  `Functor.homologySequence_exact₁`, `_exact₂`, `_exact₃` applied to the asserted
  homological functor provide all three exact spots, transported by τ.
  `homologySequenceδ_naturality` gives triangle-morphism naturality; the
  `ShiftSequence` laws give shift coherence with the standard triangle signs.
  These are bundled interfaces for the whole clause, not independently selected
  boundaries or unspecified isomorphisms in each degree.
* Clause 3: for arbitrary integers `r b n` and M, `K.IsLE r`, `M.IsGE b`, and
  `n < b-r` imply `IsZero ((T ... n).obj M)`. By `DerivedCategory.isLE_iff` and
  `isGE_iff` these are exactly the two cohomology-vanishing hypotheses. There is
  no Tor-amplitude or cohomological-dimension assumption.

### Dependencies and concrete constructions

The original statement dependencies are used as follows (module / declaration):

* `Mathlib.Algebra.Homology.HomologicalComplex` / `CochainComplex`.
* `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` publicly preserves
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses` /
  `CategoryTheory.derivedInternalHomOfUniverses`; its ordinary-module abbreviation
  is not used in this general-site statement.
* `WeilConjectures.Algebra.Homology.HomComplex` / `homComplex`, `homComplexFunctor`.
* `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` / `CochainComplex.IsKInjective`.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` /
  `SheafOfModules.overFunctor`, `overMap`, `overFunctorMap`; ring restriction is
  `Sheaf.over` on `J.over U`.
* `Mathlib.Algebra.Homology.DerivedCategory.TStructure` /
  `DerivedCategory.TStructure.t`, `DerivedCategory.isLE_iff`, `isGE_iff`.
* `Mathlib.CategoryTheory.Triangulated.HomologicalFunctor` /
  `Functor.IsHomological`, `ShiftSequence`, its exact sequence and boundary API.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic` / `DerivedCategory` and `Q`.
* `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` /
  `PresheafOfModules.sheafification`, `sheafificationAdjunction`.
* `Sheaf.CategoryTheory.RingedSiteModules` / `CategoryTheory.ringedSiteModules`.
* `def-weil-size-convention` is metatheoretic: the independent universes and chosen
  derived-category structures implement it; there is no term to import.

Already landed nodes added to stmt_deps supply constructions essential to the
normalizations, rather than duplicate private definitions:

* `def-weil-pbc-local-coefficient-localization`:
  `Sheaf.CategoryTheory.LocalCoefficientLocalization` /
  `PresheafOfModules.sectionsSMul`, `overSections`, and
  `sectionsSMul_naturality` are the universe-polymorphic constructions underlying
  the recorded coefficient multiplication. The single-universe `localCoefficient*`
  interfaces cannot apply to this general site. The helpers `rings`, `res`,
  `sectionMultiplication` and `sectionDerivedMultiplication` supply their required
  general-universe form with actual termwise data and canonical localization.
* `lem-sf-site-perfect-restriction-exact`, `lem-sf-site-perfect-overmap-exact`, `lem-sf-site-perfect-restriction-additive`,
  `lem-sf-site-perfect-overmap-additive`:
  `Sheaf.Algebra.Homology.SitePerfectModelRestriction` /
  `SheafOfModules.overFunctor_exact_ofUniverses`, `overMap_exact_ofUniverses`, `sitePerfectOverFunctor_additive`,
  `sitePerfectOverMap_additive`.
* `def-coef-hom-representative-evaluation`:
  `Sheaf.Paper.CoefficientHomRepresentativeEvaluation` /
  `WeilConjectures.coefficientHomResolution`, `coefficientHomResolutionIso`.
* `lem-sc-hom-complex-projections`:
  `WeilConjectures.Algebra.Homology.HomComplexComponents` / `homComplexπ`.

The canonical composition maps also use
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` /
`Functor.mapDerivedCategoryCompIso`, `mapDerivedCategoryNatIso`.
All recorded proof-dependency modules are imported (directly or already publicly
through the statement imports). In particular the local K-injective comparison,
resolution existence, K-injective shift/Hom bijections, exact sheafification and
homology transport, triangle exactness, and t-structure orthogonality are available.
The theorem docstring gives the complete natural-language proof: shifted local
cocycle comparison, exact sheafification, descent/naturality through K-injectives,
local long exact sequences and coherent shifts, then strict orthogonality.

### Source and edge cases

Read Stacks `sites-cohomology.tex`, `lemma-RHom-into-K-injective` (0A94) and
`lemma-RHom-well-defined` (0A95). The latter explicitly identifies the cohomology
sheaf with the associated sheaf of local derived morphisms. Integer shifts give
all degrees; exact slice restriction preserves both bounds. The node is unchanged.

On the point site with field k, K=k[-r], M=k[-b] gives the first possibly nonzero
T^n at n=b-r, so the strict inequality is essential and retained. Negative r,b,n
are permitted. K=0 or M=0 gives zero local Hom presheaves and zero sheafifications.
An empty category of site objects is allowed: no object or section is assumed to
exist. No finite-support product, bounded representative, flatness, or finite
cohomological dimension was inserted. No statement dispute was found.

### Searches and validation

Used prescribed msearch.py with group Q149 and this item:

* LeanFinder: “cohomology of derived internal Hom sheafifies local derived
  morphisms and is cohomological with vanishing below b minus r”. Eight results:
  ordinary sheaf cohomology, external Hom-complex/shifted-Hom comparisons, and
  HasExt bounds; none states the internal module-sheaf comparison with all clauses.
* Loogle: `CategoryTheory.derivedInternalHom, CategoryTheory.Functor.IsHomological`.
  Zero results (unknown identifier CategoryTheory.derivedInternalHom).
* Grep: `internalHom|InternalHom` in `CategoryTheory/Triangulated`: zero results.
* rg in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `local.*cohomological`, `localDerivedHom`, `derivedHomPresheaf`: no match for this
  theorem. The etale derivedHomPresheaf hits concern a specialized constant
  coefficient site; the local-cohomological-dimension nodes are different notions.
* Read the existing internal-Hom, local K-injective comparison, slice restriction,
  coefficient-multiplication, representative factorization and projection modules;
  use these actual constructions. Checked the new namespace against
  `dag/lean_names_upstream.json`: no collisions.

The first required saved-packet dry run failed with stuck universe constraints
at implicit calls to `resComp`, `restrictHom` and `localizedCocycle`, followed by
cascading errors, and line-length warnings. Explicit universe applications fix
these constraints without equating any universes. The final module compiles
through `scompile.py` individually in sandbox and library contexts with no
errors or warnings. No heartbeat or timeout limit was raised.

## Repair of returned H3

The independent reviewer of immutable head `a2f0b47b72ea` found that its
single-universe site, coefficient and derived categories excluded the universes
of the only citer, `lem-per-bounded-above-rhom-hyperext`, Step 1. The retained
partial repair had generalized the binders but had not yet compiled, updated
its signature record or report. This delivery completes that repair rather than
re-pushing the returned head.

The final declaration uses `uC`, `vC`, `u`, `w`, and independent `wSlice`.
`res` and `further` use the existing `overFunctor_exact_ofUniverses` and
`overMap_exact_ofUniverses`; `resComp` retains the same canonical comparison.
`sectionMultiplication` evaluates the existing `sectionsSMul` on the restricted
section `overSections`, and `sectionDerivedMultiplication` descends that natural
transformation through `Localization.liftNatTrans` with the actual
`mapDerivedCategoryFactors`. These are documented helpers of this node, as
explicitly authorized by the return, recorded in `lean.declarations`. They
introduce no choice, new hypothesis, extra postponed theorem or independent
notion. No dependency node is changed. The missing already landed statement
dependency `lem-sf-site-perfect-restriction-exact` is now listed explicitly.

Opened the reviewed citer's module
`Sheaf.Algebra.Homology.BoundedAboveRHomHyperExt`. Its
`ringedSiteRHomCohomology.{uC,vC,u,w}` and the repaired
`T.{uC,vC,u,w}` unfold to the same curry of
`derivedInternalHomOfUniverses.{uC,vC,u,w}` followed by cohomology. A temporary
consumer probe imported both actual modules and checked their equality by `rfl`
and application of `local_cohomological_bound.{uC,vC,u,w,wSlice}` with all five
universes independently bound. Both probe contexts compiled cleanly (18.6 s
sandbox, 2.4 s library). The probe was removed before delivery.
The original strict bound, normalizations and triangle clauses are unchanged.
The natural-language node statement needs no correction. The current live node
and saved packet were compared; all non-Lean fields except the already-added
statement dependencies agree. This node copy retains the current live fields.

## Second reading by Q149

Author self-check for direct dispatcher delivery; no second agent was started.
Independent mathematical review remains the maintainer's responsibility.

Reopened the node and module. Matched the independent-universe site and derived categories, commutative ring sheaf,
fixed K and every integer quantifier; local module scalar action, derived restriction,
M-naturality, module sheafification and cocycle normalization; all triangle boundary
and coherent shift clauses; and the strict lower bound. The comparison h is fixed
by the actual augmentation, preventing an arbitrary representative isomorphism.
Added `τ 0 = S.isoZero` so transporting the shift sequence identifies its degree
zero with exactly the stated T^0 and its boundary, rather than a free automorphism.
Verified the source-shift map in the boundary targets M[n+1] using
`shiftFunctorAdd' 1 n (n+1)`. All helper definitions have real data. All proofs
postponed by this delivery belong to the one named theorem. Rechecked the repaired scalar helper sectionwise: on an object W → U it
multiplies by the restriction of a, then descends through the exact restriction's
localization comparison. The cocycle equation still uses the original augmentation,
and the boundary still uses `shiftFunctorAdd' 1 n (n+1)`. The lower-bound clause
still quantifies over all integers and uses the strict inequality. No missing
clause, extra mathematical hypothesis, changed node statement or new definition
node remains.
