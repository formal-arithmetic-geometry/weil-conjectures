## Worker report

The delivery states `WeilConjectures.SpTwistedPullback.twistedPullbackReductionTower` in
`Sheaf.Paper.TwistedPullbackReductionTower`. Its proof is exactly `by sorry`.
The construction helpers are real definitions and data structures in
`Sheaf.Paper.TwistedPullbackReductionData`; their existence is part of the main theorem's
conclusion, never an additional mathematical hypothesis. No arbitrary map or Nonempty
isomorphism replaces the canonical comparison.

### Hypotheses and clauses

* Finite base field, its characteristic and algebraic closure: `D₀ : FiniteFieldDatum`;
  the record includes the base field, prime, cardinality and chosen algebraic closure.
  The prime is `(l : ℕ) [Fact l.Prime]`, with `_hlp : l ≠ D₀.p`.
* Finite extension: `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The valuation ring and all finite quotients are the
  dependency's `Padic.coefficientExtensionIntegers`, not a second construction.
* Separated finite-type k-schemes: `X Y : Over (Spec (CommRingCat.of D₀.k))`, with
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` on both structure morphisms.
  A k-morphism is `f : X ⟶ Y`; its underlying map has `IsSeparated` and
  `SmoothOfRelativeDimension d f.left`, with `d : ℕ`.
* `b`, `g`, `DX`, `RX`, `NX`, `DY`, `RY` are normalized presentations of the dependency's
  constructions. The theorem holds for every such presentation. They do not assume the
  desired comparison or any additional property of K. `hX`, `hY` are EXISTENTIAL
  conclusions deriving invertibility of ell in the residue fields, not extra hypotheses.
* Small pro-etale sites: all categories use `Scheme.ProEt.topology`. Object and morphism
  universes remain u+1 and u. Coefficients use the existing u+1 lift, without identifying
  the two site universes. Natural index n denotes the positive exponent n+1 everywhere.
* R_T and r_T: `scalarReductionSource` uses the recorded completed coefficient sheaf.
  `reduction` is `spCompletedReduction` followed by the exact section-preserving derived
  equivalence `spTowerShriekRealization`. R's ordinary levels, quotient-generator
  transitions, universal counit and K-flat computation are retained by `reductionCounit`.
* C_T and N_T: `sfIntegralConstructibleCategory` and
  `spNormalizedConstructibleTorTowerCategory` are used directly. Their predicates retain
  completeness and common finite cohomological bounds, and normalization and common Tor
  bounds respectively. `source` is integralDerivedPullback, ordinary K-flat derived tensor
  with `integralTwistLine m` in degree zero, then `shiftFunctor s`. Thus m and s range over
  all integers; no relation to d is imposed.
* Membership P(K) in C_X: the first conjunct is precisely
  `∀ K, sfIntegralConstructible ... ((source ...).obj K)`.
* Finite source: `finiteSource` is reduction of K, exact finite-system pullback,
  tensor with `line`, and shift. `line` is coherent reduction of the signed integral line
  in degree zero. `TateReduction.level` identifies its native uniformizer evaluations
  with the recorded `finiteCoefficientTwist`. `level_formula` fixes this comparison to
  the actual reduction evaluation and K-flat counit followed by the ordinary signed map.
  `ordinary_normalized` fixes its scalar-model identification on every pure tensor;
  `first_unit` fixes the first Tate quotient generator. `signed_normalized` supplies the
  existing coefficient unitor at zero, tensor formula at positive powers, and the actual
  dual-evaluation comparison for negative powers. Consequently this is the finite Tate
  twist of the node, not an arbitrary tower with isomorphic levels.
* Entire derived comparison, natural in K: q is an isomorphism of FUNCTORS into
  `SpTowerShriek.D`, the ordinary unbounded derived category of strict varying-ring
  systems. Its components are not chosen independently after evaluation.
* Canonical pullback factor: a is a whole-system natural isomorphism. The first formula
  following the existential block evaluates its hom on every flat-term K-flat representative
  P, every identification QP ≅ K and every n. It equals the existing
  `integralSystemPullbackReductionIso`, the scalar adjunct of the actual Roos projection.
  This is the same normalization as integralPullbackSystemComparison.
* Canonical tensor and shift factors: `nativeComparison` composes the recorded
  `PurReductionLimitShiftData.reduction_shift`, the coefficient calculus's
  `reductionTensor`, and tensor of a. The chosen calculus includes
  `reductionTensor_normalization` and `reductionTensor_evaluation`, which fix the balanced
  chain map on whole systems and its canonical finite evaluation. The Tate line's
  `level_formula` fixes the signed identification used in those evaluations. The shift
  data fixes the termwise shift and differential sign, including negative s.
* All quotient transitions: q lives in the derived category of entire STRICT systems.
  The native tensor comparison has its simultaneous chain-level normalization, rather
  than an appeal to faithfulness of evaluations. `CofinalModel.restrictions` quantifies
  over all j ≤ n and all horizontal site arrows, including identities and composites.
  `CofinalReduction.counit_transpose` pins the native counit before evaluation to the
  actual ordinary quotient augmentation and total-limit unit. `quotient_units` and
  `representative` preserve strict reduction and
  its universal counit; `CofinalTensor.pure` fixes every total-degree tensor summand and
  `representative` fixes the derived class of that very chain isomorphism.
* Ramification: `b.ramification_eq`, `ramification_positive`, and `ideals` fix
  ell = u*pi^e and the equality of actual ideals at all positive levels. `CofinalModel`
  restricts to e(n+1)-1 in zero-based indices. Sections, restrictions, scalar actions,
  and morphisms are retained by HEq under the identity-induced quotient identification.
  No map uses a chosen element representing the ideal. In particular replacing a
  generator by a unit multiple changes neither selected coordinate nor quotient map.
  `CofinalGeometry.mate` is the actual adjunction mate of the identity on direct-image
  sections, and `CofinalTensor` is the identity on selected tensor generators.
  The equation for `q.app K` is explicitly cofinal reduction inverse, selected
  nativeComparison, then `cofinalSourceComparison`. It is the restriction of the native
  uniformizer construction, rather than merely a comparison of separate finite levels.
* Realization: `C` has exactly the stated domain C_Y and codomain N_X. `v` is a natural
  isomorphism of entire derived towers. `realizationMap` is the actual NX.adjunction.unit
  followed by spCompletedTotalLimit applied to q and v. The presentation equivalence's
  unit and inverse unit explicitly return to the recorded tower category. The final
  conjunct asserts invertibility of that specified map for every K and writes its
  naturality equation for every derived morphism z. L_X is the dependency's total
  derived limit after exact completed-scalar restriction, never an underived limit.

### Dependency declarations used

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the actual coefficient ring,
  transition and finiteness declarations; `Padic.coefficientExtensionIntegers` is reused.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`; Mathlib's
  `Over`, `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` give the scheme data.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: completed ring sheaves,
  projections, `scalarReductionSource`, `scalarReductionExtension` and derived extension.
* `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full category.
* `Sheaf.Paper.SmoothPurityCoefficientTowers`, `SmoothPurityCoefficientTowersAbelian`,
  `SmoothPurityNormalizedTowers`, `SmoothPurityReductionTowerNormalized`:
  `spCoefficientTowers`, `SpCoefficientTowersAbelian`, `SpReductionTower`,
  `spNormalizedConstructibleTorTowers`, and `spReductionGenerator`.
* `Sheaf.Paper.SmoothPurityNormalizedEquivalence`: `spCompletedReduction`,
  `spCompletedTotalLimit`, `SpNormalizedEquivalence` and its actual adjunction.unit.
* `Sheaf.Paper.SmoothPurityTowerShriekLevels` and `SmoothPurityTowerBound`:
  `SpTowerShriek.Base`, `Geometry`, `pull`, `tensor`, `D`, and
  `spTowerShriekRealization` (definition ownership def-sp-tower-shriek-realization).
* `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `integralDerivedPullback`.
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`, `CoefficientTwistsDetailed`,
  `PurTwistSheaves`, `PurTwistCoefficientRings`: `integralTwistLine`,
  `finiteCoefficientTwist`, `purTwistIntegralModule`, `purTwistIntegralOne`,
  `purTwistIntegralQuotient` and `purTwistFiniteOne`.
* `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`: the selected
  `coefficientDerivedSystemEvaluationCalculus`, its fixed integral/system tensors,
  reduction and evaluation, `coefficientFiniteReductionModel` and total tensor models.
* `Sheaf.Paper.IntegralStrictReductionModel`: `IntegralStrictReductionModel`, including
  ordinary quotient augmentation and universal counit, not a second reduction notion.
* `Sheaf.Paper.IntegralPullbackSystemComparison`: `integralSystemPullbackReductionIso`;
  `IntegralSystemReductionFullyFaithful` and `FiniteSystemPullbackCoherence` give
  `integralSystemReduction`, finite-system pullback/evaluation and its actual adjunction.
* `Sheaf.Paper.PurReductionLimitShiftAdjunction`: `PurReductionLimitShiftData`.
* `Sheaf.Paper.SignedLineScalarTensorTower`: `SignedLineComparisonNormalized`.
* Proof imports retain ExtensionIntegersDvr, SystemLevelLeftExtension,
  IntegralOperationsPreserveConstructible, PurTwistSheafLocallyFree,
  IntegralLineReductionRestriction, OrdinaryLineDerivedScalarComparison,
  SfIntegralConstructibleTriangulated. Their proof content is summarized in the main
  theorem docstring. The proof-dependency record for
  lem-pur-normalized-scalar-comparison-realization points to an unavailable module:
  `scompile.py --source Sheaf.Paper.NormalizedScalarComparisonRealization` reported
  "Module source unavailable". It is a proof dependency, not a prerequisite notion.
  The available whole-system IntegralPullbackSystemComparison supplies the same required
  pullback normalization; the missing module is not imported or copied.

### Edge cases

Checked m=0 (coefficient unitor), m=1, m=-1 and general negative m (actual internal dual
and signed evaluation), s=0 and both signs of s (the recorded cochain shift), d=0,
zero K, and empty X or Y. No nonemptiness hypothesis is introduced. At j=n the strict
quotient map is the identity; arbitrary j≤n and triple composites are included. For
ramification e=1, selected index is n; for e=2, ell level n=0 selects uniformizer index1,
and level n=1 selects index3. Positivity ensures no exponent-zero quotient is used.
No quotient map is assumed flat. No additional equality of site universes is imposed.
All maps and equations take place in derived categories, not just cohomology.

### Searches and compilation

`msearch.py leanfinder` with "Derived reduction of completed pullback tensor a Tate line
and shift is naturally isomorphic as entire coefficient towers" returned scheme tensor
congruences and Kaehler differentials, no exact result. `msearch.py loogle` on
`CategoryTheory.Functor.mapIso, CategoryTheory.NatIso` returned no match (NatIso is not a
standalone declaration); the corrected `CategoryTheory.Functor.mapIso` query returned
12 generic isomorphism mapping lemmas. `msearch.py grep` on
`twistedPullback|TateTwist|normalized.*tower` returned only unrelated normalized-trace files.
`msearch.py leansearch` on canonical cofinal restriction preserving pullback and signed
Tate tensor returned eight generic results (sheafPullback exactness, derived localization,
complex restriction, ring tensor), none this construction. Raw search records are copied
into the new definition node. Project rg searches on WeilConjectures and Sheaf found
no exact statement; the relevant existing coefficient, signed-line and strict reduction
APIs above were read and reused. DAG searches and blueprint_refs.py search found no
owning definition for the cofinal comparison package. The latter returned zero matching
blueprint nodes; `ancestor` returned det-sp-integral-adjunction-bijection.

Every compile used the prescribed scompile.py wrapper. Initial universe and inaccessible
private helper errors were repaired. The final split modules compile independently in
an overlay, with no errors or warnings. The split keeps each compiler invocation within
the required limit; there is no global build and no direct compiler invocation.

## Second reading by NR

The maintainer's independent second reader (cc review service, 2026-10-25) wrote
this section in place of the worker's self-check, which the worker itself described
as not an independent reading (delivery-errors H11). Both Lean modules and both node
records are unchanged.

Node statement, item by item, against the delivered Lean:

| Node | Lean | Verdict |
|---|---|---|
| k0 finite of char p, k = algebraic closure, prime ℓ ≠ p | `D₀ : FiniteFieldDatum.{u}`, `D₀.k`, `[Fact l.Prime]`, `_hlp : l ≠ D₀.p` | exact |
| E/Q_ℓ finite, O_E | `E : Type u`, `[Algebra (Padic l) E] [FiniteDimensional ..]`; the recorded `Padic.coefficientExtensionIntegers` | exact |
| X, Y separated finite type over k | `X Y : Over (Spec (.of D₀.k))`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` of `.hom` | exact (finite type = lft + qc) |
| f smooth separated, pure rel. dim d ≥ 0 | `f : X ⟶ Y` (k-morphism), `[IsSeparated f.left]`, `d : ℕ`, `[SmoothOfRelativeDimension d f.left]` | exact |
| R_T, B_{n,T}, r_T, L_T | `scalarReductionSource`; `reduction` = `spCompletedReduction ⋙ spTowerShriekRealization`; `spCompletedTotalLimit`; n ↦ exponent n+1 | exact (det-sp-normalized-equivalence objects) |
| C_T, N_T | `sfIntegralConstructibleCategory`, `spNormalizedConstructibleTorTowerCategory` | exact |
| P_{m,s}(K) = f^*K(m)[s], m, s ∈ ℤ | `source`: `integralDerivedPullback`, K-flat derived tensor with `integralTwistLine m` in degree 0, `shiftFunctor s` | exact up to the advisory below |
| P_{m,s}(K) ∈ C_X | first conjunct | exact |
| q : r_X P ≅ (f^*_{B_n}(K⊗B_n)(m)[s])_n, natural, whole tower | `q : source ⋙ reduction ≅ finiteSource`, an iso of functors into `SpTowerShriek.D` (strict systems, all transitions) | exact |
| component = pullback comparison, balanced line tensor, shift | `nativeComparison` = `reduction_shift` ≫ `reductionTensor` ≫ tensor of `a`; `a` pinned on every good representative and every n by `integralSystemPullbackReductionIso` (same normalization as landed `integralPullbackSystemComparison`) | exact |
| finite Tate twist B_n(m) | `line` = r_X(O_E(m)[0]); `TateReduction.level` pinned to reduction evaluation, K-flat counit and the signed ordinary comparisons | accepted |
| restriction to levels en; generator-independent | `CofinalModel` selects e(n+1)-1, sections/maps/scalars by HEq; only `b.ramification` and ideal equalities enter | exact |
| q equals the transported uniformizer construction | `q.app K = cX.derived⁻¹ ≪≫ FX(nativeComparison) ≪≫ cofinalSourceComparison`; cX, G, T pinned by representative, mate and pure-tensor clauses | exact |
| realization L_X(v)L_X(q)u_P natural iso for every C : C_Y ⥤ N_X, v | `realizationMap` = `NX.adjunction.unit` then total limit of q ≫ v (with the presentation unit inserted); `IsIso` for every K and the naturality square for every z | exact |
| derived-category statement, not per degree | all clauses are isomorphisms/equations in derived categories | exact |

Edge cases: m = 0, m < 0, s of both signs, d = 0, K = 0, empty X or Y, ramification e = 1
and e > 1 (index e(n+1)-1 ≥ 0 since e > 0), j = n transitions. None is excluded.

Searches: rg for twistedPullback, CofinalReduction, TateReduction and twist-reduction
packages in lean/Sheaf and lean/WeilConjectures; DAG lean records owning the used
declarations. No owner of the cofinal package exists; the reused interfaces are the
recorded ones.

Advisories (not faults): (1) `source` renders K(m) by the coefficient calculus' K-flat
derived tensor with the recorded line, not by the recorded `sfIntegralTwistingFunctor`
(exact sheaf tensor); for the flat line these are canonically isomorphic, and it is
the M ⊗^L L^[m] of proof step 2, but a citer stated with `sfIntegralTwistingFunctor`
must insert that comparison. (2) `∃ tate : TateReduction` is not referenced by the other
clauses; it only asserts the normalized line reductions. (3) Declarations owned by nodes
not in the item's stmt_deps (SpTowerShriek.Base/Geometry ← det-sp-tower-shriek-levels,
SpReductionTower ← det-sp-reduction-tower-normalized, integralSystemReduction,
finiteSystemDerivedPullback, integralOperationsGoodComplex,
proEtaleConstantRingDerivedPullback, `coefficientDerivedSystemEvaluationCalculus.choose`)
follow the landed practice of this chapter.

No compile was run by the second reader: no Lean file changed.

## New nodes

`def-sp-twisted-pullback-reduction-data` owns the explicit source/reduction/finite-source
functors, cofinal presentation/reduction/geometry/tensor normalization data, native and
cofinal comparison composites, actual reconstruction composite, and Tate reduction
normalization. These are precisely the helper data needed to type the source's canonical
entire-tower comparison. They reuse the existing notions of strict reduction, coefficient
calculus, signed lines, normalized shifts, finite-system inverse image, and completed
reduction/limit adjunction. The source is the latest blueprint Purity paragraph, expanded
in the item's proof steps 1–7. The searches above found these component notions but no
such normalized cofinal comparison package. Its definition module contains no sorry.
The main item's stmt_deps gains this new definition and the already landed recorded
interfaces appearing directly in its signature; no existing dependency record changes.
