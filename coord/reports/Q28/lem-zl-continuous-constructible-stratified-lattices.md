## Worker report

The module `Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices` states
`WeilConjectures.StratifiedContinuousLattices.continuous_constructible_stratified_lattices`.
It has one postponed theorem, with the complete seven-step proof plan from the node.
The helper structures unpack this theorem's conjunctions and existential data; every
helper definition has real data and uses the already recorded canonical construction.
There are no extra axioms, private replacement notions, dependency repairs, or statement
corrections. The original TeX statement is unchanged.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
|---|---|
| q = p^a, finite field and its algebraic closure k | `D : FiniteFieldDatum.{u}` and `D.k`; the existing datum contains p, a, q and the fields |
| prime ell different from p | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)` |
| finite E/Q_ell with its extended norm, integers A and uniformizer | `E : Type u`, `NormedField E`, `NormedAlgebra ℚ_[l] E`, `FiniteDimensional ℚ_[l] E`; the existing `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer` and `coefficientExtensionIdeal` |
| separated finite-type k-schemes | `PerAdic.Base D.k`, whose fields are the structure map, locally finite type, quasi-compact and separated; the empty scheme is allowed |
| small pro-etale site | `Scheme.ProEt` and `ProEt.topology`; its object universe is u+1 and arrow universe u, not identified |
| B is the inverse limit of positive residue constant sheaves | `pbcAdicCompletion X (pbcIntegralDatum l E)`; index n encodes exponent n+1 |
| E_W is localization of B at the uniformizer | `Coefficients.integral`, `localization`, `localization_normalized` and `rational_values` give the canonical continuous integral coordinates and the normalized localization into `rationalCoefficientSheaf` |
| pulled condensed rings and canonical charts | `condensedRingObj (Profinite.continuousCoefficientRingObj A/E) X`; `chart` is the published `ContinuousRingUniverse.comparison` followed by the inverse of `continuousSectionRingIso`; `integral_chart` and `rational_chart` assert invertibility |
| every finite projection is reduction | `Coefficients.finite`, `finite_constants`, `integral_reduction`; constants and all evaluations are fixed, including all positive exponents |
| rational chart is localization and inclusion square commutes | `localization_normalized`, `rational_values`, `Coefficients.scalar`; `CoefficientFamily.inclusion_square` uses the actual canonical `continuousInternalScalarMapUniverses` |
| locally closed coefficient restriction | `Restriction.integral`, `rational`, `integral_normalized`, `rational_normalized`, `square`; the maps are the actual continuous-function pullback maps transported by the specified coefficients |
| successive restrictions | `Family.composition`, separately for the integral and rational maps after `proEtaleRingInverseImageComp` |
| finite coefficient extensions, including ramification | `FieldChange` with actual continuous integer map, pointwise rational values and the commuting scalar square; `quotient_normalized` quantifies over compatible exponents m+1,n+1 and uses `Ideal.quotientMap`, never equating uniformizers |
| coefficient extensions commute with restriction and composition | `Family.field_restriction`, `field_composition`; both integral and rational equations are included |
| internal and sectionwise module encodings | the existing `continuousLatticeModuleEquivalenceUniverse`, `completedContinuousModuleEquivalence`, and `continuousFieldModuleEquivalenceUniverse`, with the rational coefficient isomorphism transported by `ringModuleEquivalenceOfIso` |
| identity underlying sheaves, maps and actions | `Encoding.sections`, `identity_sections`, `identity_maps`; the section action is the dependency's real section-action construction, not chosen extra module data; fully faithful identity sheaf maps preserve submodule inclusions |
| lisse iff locally finite free, allowing varying and zero ranks | `Encoding.lisse : LisseCriterion X R`, using the recorded `LocallyFree` scheme-cover predicate and `SheafOfModules.IsFiniteLocallyFree` |
| inverse images commute with encodings | `Encoding.restriction`, `restriction_unit`; `internalPullUnit` is the abelian inverse-image unit followed by the actual internal scalar-extension unit, and the other side is `ContinuousRational.moduleUnit` |
| ordinary scalar extensions commute, r tensor m maps to r tensor m | `Family.ordinary_scalars` quantifies over arbitrary commutative internal coefficient ring sheaves and their ring maps; `OrdinaryScalars.extension` and `pure_tensors` compare the actual `Mod.extendScalars` with `pbcExtend (sectionRingMap ...)`; the formula is on every scalar s and module section m, using the genuine adjunction unit and target module action |
| integral-to-rational encoding comparison | `ScalarComparison.restriction`, `restriction_identity`, `extension`, `tensor_unit`; the comparison is fixed on the unit generator, hence on every pure tensor by linearity |
| constructible F | `Family.strata` quantifies over F and a supplied `FiniteLocallyClosedStratification S`, with `_hS` asserting local finite freeness on each stratum. Quantifying over every witness is the witness-explicit form of the constructibility assumption |
| finite refinement of the lisse partition | `Stratified.refinement`, `parent`, `factor`, `factor_immersion`, `factorization`; partition, coverage, disjointness and locally closed images are inherited from the recorded finite stratification structure |
| same coefficient field E | all lattices and all restrictions in `Stratified` use its single parameter E; no field extension occurs in the lattice existence clause |
| genuine embedded internal integral lattice | `Lattice.moduleObject`, `internal_lisse`, `internal_inclusion`, `internal_mono`, `internal_localization`; the last field is `IsIso (Mod.extendHom ... internal_inclusion)`, the map induced by this specific inclusion |
| its encoded B-module inclusion and lisseness | `Lattice.inclusion`, `same_inclusion`, `lisse`, `mono`, with the actual rational encoding counit and restriction comparison |
| the inclusion induces L[1/varpi] isomorphic to F | `Lattice.localization` is `IsIso` of the actual adjunction-transposed inclusion, rather than an unrelated existence of an isomorphism; the specified coefficient localization identifies ordinary extension with inversion of varpi |
| reduced strata and preservation under reduction | `Stratified.reduced`, `same_length`, `reduction`, `reduced_immersion`, `isReduced`; each domain is isomorphic to the actual nilradical subscheme and its immersion is exactly the composite with the reduction inclusion |
| reduction preserves the same lattice inclusion and localization | `Stratified.reduction_lattice : LatticeRestriction ...`; its `integral_iso` and section equation `same_inclusion` identify the pulled inclusion and therefore its induced extension map |
| every further locally closed restriction | `Stratified.further` uses the same `LatticeRestriction`, whose coefficient maps are pinned by `integral_normalized` and `rational_normalized`; its `pulled` field includes lisseness, monicity and the inclusion-induced localization isomorphism |
| empty partition, zero lattices and no global lattice | `Stratified.empty` sets the refinement length to zero for an empty base; the reduction has the same length. Rank zero is included in both freeness predicates. A monomorphism into zero forces the lattice to be zero. There is no global lattice field in `Family` or `Stratified` |

The normalized unit and pure-tensor formulas determine the natural comparisons uniquely,
so successive tensor comparisons are balanced tensor comparisons. They also fix the
localization after restriction: naturality of scalar-extension adjunction sends the
pulled inclusion to precisely the pulled localization map. We impose no equality of
site and coefficient universes. `EssentiallySmall.{u+1} X.ProEt` is constructed by
`essentiallySmallSelf.{0}`; this explicit size derivation repairs elaboration without
adding a mathematical hypothesis. Locally closed coefficient pullback in `Encoding`
is asserted under `IsNoetherian X`, which follows for the bases and strata used here.
The universal coefficient construction itself does not require noetherianity.

Dependency declarations used (the node's recorded modules were opened and signatures
and docstrings read; the universe variants are landed dependencies added to stmt_deps):

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber` / `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` / `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties`: `None` / `None`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale` / `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` / `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `sk-def-sfb-pulled-back-coefficients`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` / `AlgebraicGeometry.ProEtale.coefficientRing`.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod` / `CategoryTheory.Mod`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules` / `CategoryTheory.ringedSiteModules`.
- `lem-weil-pbc-continuous-coefficient-realizations`: `Sheaf.Paper.ContinuousCoefficientRealizations` / `AlgebraicGeometry.ProEtale.chartComparison_naturality`.
- `lem-per-continuous-rational-derived-realization`: `Sheaf.Paper.ContinuousRationalDerivedRealization` / `AlgebraicGeometry.Scheme.ContinuousRational.continuous_rational_derived_realization`.
- `def-weil-pbc-continuous-coefficient-module-encoding`: `Sheaf.Paper.ContinuousCoefficientModuleEncoding` / `AlgebraicGeometry.ProEtale.CondensedRing.continuousRingModuleEquivalence`.
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`: `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence` / `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`.
- `def-constructible-stratification`: `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification` / `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`.
- `def-sf-proetale-locally-finite-free-module`: `Sheaf.Paper.ContinuousLocallyFreePullback` / `AlgebraicGeometry.ProEtale.CondensedRing.LocallyFree`.
- `def-sfb-continuous-coefficient-module-equivalence-universe`: `Sheaf.Paper.ContinuousModuleEncodingUniverses` / `AlgebraicGeometry.ProEtale.CondensedRing.continuousFieldModuleEquivalenceUniverse`.
- `def-per-adic-base-stages`: `Sheaf.Paper.AdicHeartPullbackFibres` / `AlgebraicGeometry.Scheme.PerAdic.Base`.
- `def-weil-pbc-continuous-constructible-module`: `Sheaf.Paper.ContinuousConstructibleModule` / `AlgebraicGeometry.ProEtale.continuousCoefficientInverseImageMap` (the canonical-map helper listed in that node’s `lean.declarations`; its constructibility predicate is unused).
- `def-weil-pbc-continuous-scalar-map-universes`: `Sheaf.Paper.ContinuousScalarEncodingUniverses` / `AlgebraicGeometry.ProEtale.CondensedRing.continuousInternalScalarMapUniverses`, with its proved `continuousInternalScalarMapUniverses_isMonHom` instance.
- `def-weil-pbc-completed-continuous-module-encoding-universes`: `Sheaf.Paper.ContinuousModuleEncodingUniverses` / `AlgebraicGeometry.ProEtale.CondensedRing.completedContinuousModuleEquivalence`.

`def-weil-scheme-morphism-properties` is a recorded convention node rather than a
module; the actual Mathlib scheme morphism classes are the fields of `PerAdic.Base`.
The proof imports are the node's completion, immersion restriction, chart naturality,
coefficient composition, section tensor, site inverse-image tensor, encoding scalar
extension/local-freeness, stratified lattice, embedded lattice comparison, reduction
and locally-free pullback modules. The proof docstring follows their seven uses in
order. Mathlib leaf matches are used as recorded: finite-type noetherianity,
noetherian-space minimal closed subsets, immersion finite type/base change,
locally noetherian finite type, morphism permanence and the spectral norm extension.

Source check: Bhatt--Scholze 6.8.13 first paragraph constructs lattices on a finite
stratification at the given finite field E, using 6.8.4(6); 6.8.2 gives completion and
localization; 6.8.15 gives restriction compatibility. Read the current blueprint's
`sec-deligne-laumon-general/sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`,
paragraph 6, under `literature/blueprint/latest/`. No change to its unit statement is
needed.

Edge cases checked: empty T and empty indexing sets; F=0 and rank zero; disconnected
schemes with nonconstant finite local ranks; nonreduced strata and their nilradical
reductions; identity and successive restrictions; identity and successive coefficient
extensions; ramified extensions with different uniformizers and compatible unequal
powers; arbitrary (not necessarily constructible, complete or finitely generated)
modules in the ordinary encoding/scalar-extension clause; original coefficient field
and the full small-site universes. No global lattice or extra connectedness, smoothness,
properness, constant rank, nonemptiness or field enlargement is assumed.

Searches made before writing:

- msearch LeanFinder: “Constructible continuous l adic module sheaf finite reduced
  locally closed stratification lisse embedded integral lattices coefficient
  normalization”: eight unrelated local-cohomology/condensed hits, no exact statement.
- msearch Loogle: `SheafOfModules.IsFiniteLocallyFree, IsLocalization`: no hits;
  the service reported the first identifier unknown. This failed query was followed
  by direct source inspection and the other searches, not treated as absence proof.
- msearch grep in Mathlib: `stratified.*[Ll]attice|[Ll]attice.*stratif`: zero hits.
- msearch LeanSearch: “finite stratification of a constructible l adic sheaf with
  embedded integral locally free lattices”: eight finite-type/presentation hits,
  none stating the normalized coefficient-and-lattice conjunction.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: stratification/lattice and continuous
  coefficient/encoding patterns. Found and reused all listed canonical constructions;
  the existing internal stratified-lattice theorem omits the constructible-sectionwise
  assembly and normalized reduction/pullback clauses of this node.
- Node-id search in `lean/WeilConjectures`: no existing declaration for this exact node.
- DAG/module searches located the already landed universe encodings, continuous scalar
  map, generic LocallyFree predicate and finite-type base record. Their owning nodes
  are cited instead of adding replacement definition nodes.

No STATEMENT-DISPUTED marker or source fault is warranted. One new definition-node attachment is added as described below; no dependency
module or replacement construction is needed. The full signature is recorded verbatim in lean.statement.

## Returned delivery repair

H2 (head 293beea9b3d4): added `def-weil-pbc-continuous-scalar-map-universes`,
attaching `continuousInternalScalarMapUniverses` and its proved `IsMonHom` instance
with `existing: true`. The item's `stmt_deps` replaces the theorem node
`lem-weil-pbc-continuous-scalar-encoding-universes` by this definition node. The
actual imported module and map stay the published canonical ones. The new node
deliberately excludes the exactness/scalar-comparison theorem. The main-module
docstring and `lean.note` now name the correct owner. This is an ownership repair,
not a change to the mathematical statement independently accepted in the return.

Advisory: `lean.note` explains that `Family.strata` uses the explicit arbitrary
witness S of constructibility and its locally finite free strata, the witness-explicit
form of `ContinuousRational.IsConstructible`. No second constructibility predicate
is defined. `def-weil-pbc-continuous-constructible-module` is retained because its
`continuousCoefficientInverseImageMap` is directly used in `continuousPull`,
`Encoding.restriction_unit`, `Restriction.integral_normalized` and
`LatticeRestriction.integral_normalized`; its predicate `IsContinuousConstructible`
is not used. Keeping this definition dependency therefore records a real canonical
map used by the statement.

Compared the retained packet with the current main node (which still has no Lean
record) and the returned packet's declaration list; only the authorized ownership
attachment, added dependency, explanatory notes/docstrings and report changed.
The final theorem signature and all fields of `Family` are unchanged.

## New nodes

`def-weil-pbc-continuous-scalar-map-universes` defines the actual internal integral
coefficient inclusion by the canonical integral chart, postcomposition with
O_E → E on continuous functions, and the inverse field chart, with the already
proved ring-hom instance. Source: BS Lemma 6.8.2(2). It attaches the existing
`Sheaf.Paper.ContinuousScalarEncodingUniverses` declarations with `existing: true`,
so requires no new module. DAG search found only the scalar-encoding theorem node;
blueprint search found no definition node. Mathlib LeanSearch and LeanFinder each
returned eight unrelated results and Mathlib grep returned none. Source rg found
the exact existing definition and instance in that module, which are reused. The
new node records those searches verbatim and adds no assumptions, choices or sorry.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
