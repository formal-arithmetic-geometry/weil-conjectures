## Worker report

The item is stated by
`AlgebraicGeometry.ProEtale.CompleteCompactificationLimit.complete_compactification_limit_realization`
in `Sheaf.Paper.CompleteCompactificationLimitRealization`. Its proof is the sole `sorry` in
the delivery. All definitions have real data; the theorem docstring supplies the complete
five-step natural-language proof. A new definition node owns the support module, since the
ordered natural transformation and the normalized completed reduction-limit presentation
were not previously exposed together. The original item's mathematical statement is
unchanged.

Clause-by-clause reading:

* A prime and finite extension: `(l : ℕ) [Fact l.Prime]`, `(E : Type u) [Field E]`,
  `[Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. The integer ring and ell-power ideal
  are the recorded `Padic.coefficientExtensionIntegers` and `spEllIdeal`, not new rings.
* Positive quotient level n+1 is Lean index n, including n=0. `finiteCoefficients`, `rings`
  and `transitions` reuse the existing constant quotient rings and actual factorPowSucc.
  `Integral` is the ordinary unbounded derived category over `scalarReductionSource`;
  this is the same completed coefficient ring identified in the recorded reduction node
  with the section realization of the pulled-back integral ring. There is no discrete
  constant O substituted for this completed sheaf.
* `D T` and `r T` are the recorded `SpCoefficientTowersAbelian` and `SpReductionTower`
  presentations. The quantified `b : SpTowerShriek.Base` and `o : ...Operations b` are the
  recorded simultaneous section-model presentations, retaining their section and transition
  normalizations. These are presentation parameters, not assumptions that this comparison
  is an isomorphism. The theorem concludes the existence of all additional comparison data.
* `reduction` is exactly `spCompletedReduction`; `forgetting` is the existing
  `spCompletedStrictTower`; `totalLimit` is the existing `spCompletedTotalLimit`, namely
  exact forgetting followed by the fixed-ring total derived inverse limit. No diagram in
  a derived category, chosen triangulated cone, or separate system of objects is used.
* `LimitPresentation` records exactness of this existing forgetting functor and the
  reduction/limit adjunction. Its `ordinaryEvaluation`, `tensor_normalized` and
  `evaluation_normalized` fix the finite scalar identification on actual tensor generators
  and universal derived counits, on every complex. `unit_projection` then fixes each
  projection of the specified completion unit to the existing scalar adjunction unit.
  The theorem asserts existence of these normalized presentations, rather than assuming
  their existence or supplying an arbitrary completion map.
* `Evaluation.ordinary` and `Evaluation.sections` identify the two recorded strict
  evaluation presentations by the identity on section elements. These data too are
  concluded existentially, for all schemes before the compactification is considered.
* `X`, `c.Z`, `Y` have the three `CompactSpace` and three `QuasiSeparatedSpace` hypotheses.
  The three residue-field `IsUnit (l : ...)` clauses express invertibility of ell on each
  scheme. No base field, finite type over a field, smoothness or constructibility is added.
* `c : Compactification f` supplies `c.i`, `c.g`, the factorization, open immersion and
  properness. The additional `QuasiCompact c.i` is explicit. `image c` is exact open
  extension localized first, followed separately by right-derived proper direct image.
  The recorded lower-shriek declaration has precisely this separately derived meaning;
  here it is expressed in the section-module presentation of the same coefficient sheaf.
* `towerOpen` and `towerPush` transport the stipulated simultaneous ordinary section
  operations and respectively localize and right derive them. Their domains are ordinary
  unbounded derived categories of actual strict semilinear systems. They are not formed
  by independently choosing a functor at each quotient.
* `ScalarSquares` uses the actual `spCompletedEllCommProjection`, and `coefficientChange`
  has that map as its real data. `ScalarComparison.open_normalized` uses the existing
  inverse open restriction comparison, fixed by the open adjunction; its finite evaluation
  uses `finiteOpen`, the canonical adjunction-uniqueness comparison. `push_normalized`
  uses the inverse of the existing ringed restriction/direct-image comparison, with the
  actual coefficient square. `derived_normalized` fixes the derived push comparison by
  the two composition units on every complex. Thus none of these is a bare arbitrary
  isomorphism or chosen map having only the right source and target.
* `IsInput M` says exactly `IsIso (completionUnit.app M)` and
  `∃ k : ℤ, (reduction.obj M).IsGE k`. This is D+ without a uniform chosen bound. It puts
  no normalization, finite Tor, finite support or constructibility condition on M or output.
* The conclusion gives an actual isomorphism `α` from `image.obj M` to
  `totalLimit.obj (towerPush.obj (towerOpen.obj (reduction.obj M)))`. Its hom is equal to
  `comparison.app M`. The latter was defined on the entire unbounded source as a natural
  transformation. Consequently this equality supplies the canonical natural family on
  all stated inputs; objectwise choices of α do not introduce choices of maps.
* `comparison` is the literal ordered composite: whisker the specified completion unit
  with `image`; apply the constant-diagram/open mate `openLimit`; apply the geometric
  adjunction mate `pushLimit`; apply the total limit to `scalarComposite`. The latter
  is the derived strict open comparison followed by the derived strict push comparison.
  Associators only change parentheses. `pushLimit` is a real conjugate of the identity
  constant-tower/inverse-image square under the existing geometric and limit adjunctions.
* The two universal projection identities for `openLimit` and `pushLimit` are conclusions.
  `w` is normalized by the actual direct-image computations on K-injective strict towers
  (`IsFixedPushEvaluation`), not just by its type. The final equality states
  `α.hom ≫ π_n = image.map (quotientAugmentation M n) ≫ finiteScalarComposite ... n`.
  `quotientAugmentation` is literally `η_M ≫ π_n`; after the existing exact forgetting
  evaluation isomorphism `LimitPresentation.unit_projection` identifies it with the
  actual scalar adjunction unit. `finiteScalarComposite` consists of the canonical open
  and push evaluation inverses followed by evaluation of the strict scalar composite.
* Every scalar map is a natural transformation or isomorphism between functors on
  actual strict systems, or its localization/right derivation. This retains all iterated
  quotient transitions including equal indices. We never infer equality of arbitrary
  derived tower morphisms from equality of their evaluations.

Dependency declarations used (names are the actual declarations read in the source):

* `SmoothPurityReductionTowerNormalized`: `SpReductionTower`, `spReductionGenerator`,
  `spIntegralSectionRing`, `spIntegralModuleEquivalence`, `spIntegralAbComparison`.
* `SmoothPurityNormalizedEquivalence`: `spCompletedReduction`, `spCompletedStrictTower`,
  `spCompletedTotalLimit`, `spCompletedTotalProjection`, `spCompletedForgettingEvaluationIso`.
* `SmoothPurityCoefficientTowersAbelian`: `SpCoefficientTowersAbelian`,
  `spCoefficientEvaluation`, `spDerivedCoefficientEvaluation`, `spDerivedCompletedEvaluation`.
* `SmoothPurityTowerShriekLevels`: `SpTowerShriek.Base`, `Operations`, `R`, `ev`,
  `finiteOpenAdjunction`, and the ordinary normalized open/push evaluations.
* `SemilinearDerivedSections`: the existing strict sequence-site system operations;
  these are the section calculus underlying `SpTowerShriek`.
* `IntegralCompactSupportCoefficientData`: `PurCompactSupport.completed`, `Coefficients`,
  `Change`, `openExtension`, `openAdjunction`, `openRestriction`, `openRestrictionMap`.
* `CompleteProetaleStrictTowerRealization`: `cbcRealizationLimitAdj`, `cbcRealizationConst`,
  `cbcRealizationLimitMap`; only these general constructive helpers, not its specialized
  compact-support theorem, are used.
* `CoefficientRingedSequenceSite`: `coefficientConstantTowerLimit`,
  `coefficientConstantTowerEvaluation`, `coefficientConstantTowerProjection`, through the
  recorded `spCompletedTotalLimit` API.
* `ProEtaleRingSheafChangeAdjunction`: `proEtaleRingRestrictionDirectImage`,
  `proEtaleRingRestrictionDerivedDirectImage` and the actual geometric module adjunctions.
* `WeilConjectures.Compactification.RefinementCategory`: `Compactification` with open,
  proper and factorization fields. The node's upstream separately derived lower shriek
  is `ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`.
* The coefficient extension is `Padic.coefficientExtensionIntegers`, and completed
  coefficient projections are `spCompletedEllCommProjection`. The derived completion
  dependency is read in `Sheaf.SixFunctors.ProEtale.DerivedCompletion`; the theorem uses
  the expressly specified reduction/limit unit as the node requires, not a new predicate
  asserting a comparison that is to be proved.
* `Functor.mapDerivedCategorySquareIso`, `mapDerivedCategoryFactors`,
  `mapDerivedCategoryCompIso`, `rightDerivedFunctorUnitQ`,
  `rightDerivedFunctorObjQIso`, and `conjugateIsoEquiv` are the constructive derived
  localization/adjunction machinery. All variables and universes are explicitly bound.
* Every original proof-dependency module is explicitly imported by the theorem module.
  In particular the exact-product, ringed-open product, diagram scalar, sequence-limit,
  derived composition, countable product, localization and ringed push-limit results
  support exactly the five proof steps documented on the theorem.

Edge cases checked before finalizing: M=0; empty source or ambient; identity open and
identity proper map; clopen open; the first positive quotient n=0; equality and arbitrary
iterated quotient transitions; complexes bounded below in an arbitrary integer degree.
No formula uses division by n, excludes identities, assumes a finite support condition,
or concludes normalization of the proper-image tower. Completeness is precisely the
invertibility of the specified normalized unit, including the identity case.

Searches: `msearch.py` leanfinder for a derived complete proetale compactification image
as inverse limit returned only condensed/ordinary completion declarations (8 hits), not
this statement. Loogle for `rightDerivedLowerShriekOfCompactification` returned 0;
local rg locates the upstream separately derived functor definition, which supplies the
meaning of the source composite but does not assert this limit realization. Mathlib grep
`compactification.*limit|limit.*compactification|complete.*realization` in CategoryTheory
returned 0. Further leanfinder, loogle, leansearch and grep for the normalized comparison
word are recorded verbatim in the new node. Project rg found the already-landed
`IntegralCompactificationComparisonBridge`, restricted to constructible objects and
finite-type schemes over a field, and `CompactSupportScalarLimitReduction`, about a
finite extension of coefficients; neither has this unrestricted complete-input statement.
`IntegralDirectImageTower` is the downstream citer, so it is deliberately not imported.
DAG searches and a dependency traversal checked that no added dependency reaches this
item. The newest blueprint `literature/blueprint/latest` paragraph (2) and local Stacks
proetale.tex lemma-j-shriek-limits agree with the node. No statement dispute or correction.

Compilation: scompile.py compiled each of the two modules separately, in dependency
order, against the live published library. Support: 53.4 seconds; theorem: 19.5 seconds.
The support has no sorry; the theorem's single sorry is expected at stage 2. The support
was split out to keep each compile below 60 seconds. No local or global build was run.

## Second reading by NF

Independent second reading by the maintainer reviewer. The delivered section said it was a
self-review ("the dispatcher explicitly prohibits spawning another agent"). I read the item
node, the new node def-sp-complete-compactification-limit-comparison, the records of all
eleven stmt_deps, the two modules `Sheaf.Paper.CompleteCompactificationLimitSupport` and
`Sheaf.Paper.CompleteCompactificationLimitRealization`, and the declarations they use:
`SpCoefficientTowersAbelian`, `SpTowerShriek.Base` and `Operations`,
`SpNormalizedEquivalence`/`spCompleted*`, `PurCompactSupport.completed`/`openExtension`/
`image`/`openRestrictionMap`, `cbcRealizationLimitAdj`/`Const`/`LimitMap`,
`coefficientConstantTowerLimit`/`Projection`, `proEtaleRingDerivedDirectImage` and
`Compactification`.

The node's statement as a list, with the Lean that renders it and the verdict:

1. A prime ℓ and finite E/ℚ_ℓ with ring O: `(l) [Fact l.Prime] (E : Type u) [Field E]
   [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Correct.
2. A_{n,T}=(O/ℓ^n)_T and R_T = lim A_{n,T}, the pulled-back integral ring: `Integral T` is
   the derived category of `scalarReductionSource`, the ring of the recorded
   det-sp-reduction-tower-normalized; `finiteCoefficients n` is level n+1 with the
   constant-ring pullback isomorphisms. Lean index n is quotient n+1. Correct.
3. r_T, derived reduction: `reduction = spCompletedReduction D r`, the recorded one. Correct.
4. L_T = Rlim ∘ Res: `totalLimit = spCompletedTotalLimit`, i.e. exact forgetting followed by
   the K-injective total limit `coefficientConstantTowerLimit`. Correct.
5. Ordinary unbounded derived categories and simultaneous section-model tower operations:
   `towerOpen` (localized) and `towerPush` (right derived) of the transported
   `SpTowerShriek.Operations` functors on `spCoefficientTowers`. Correct.
6. X, X̄, Y qcqs, ℓ invertible: three `CompactSpace` and three `QuasiSeparatedSpace`
   arguments, and `∀ x, IsUnit (l : residueField x)` on each scheme. A local ring element is
   a unit iff its residue is, so this is invertibility of ℓ. Correct, nothing stronger.
7. f = pj, j a quasi-compact open immersion, p proper: `c : Compactification f`
   (`comm`, `IsOpenImmersion c.i`, `IsProper c.g`) and `QuasiCompact c.i`. Correct. No finite
   type, base field or separatedness is added.
8. Rf_!^c = Rp_{*,R} j_{!,R}, separately derived: `image c = (openOrd c.i).mapDerivedCategory
   ⋙ (pushOrd c.g).rightDerivedFunctor`. This is definitionally
   `PurCompactSupport.image (completed l E) c` (abbrev `proEtaleRingDerivedDirectImage` =
   rightDerivedFunctor of `proEtaleRingModuleDirectImage`). Correct.
9. M derived ℓ-complete (specified unit η_M invertible): `IsInput.1 = IsIso
   (completionUnit.app M)`, where `completionUnit = a.adjunction.unit`. Two adjunctions
   r ⊣ L with the same functors differ by an automorphism of r, so invertibility does not
   depend on the choice of `a`. Correct.
10. r_X M ∈ D^+: `∃ k, (reduction.obj M).IsGE k`. Correct, no uniform bound.
11. Canonical natural isomorphism α_{c,M}: `∃ α, α.hom = (comparison …).app M`. `comparison`
    is a natural transformation on the whole unbounded category, so α is natural in M.
    Correct.
12. Normalization, in order: η, then the open/limit comparison, then the push/limit
    comparison, then the scalar comparisons: `comparison` = whiskerRight completionUnit image
    ≫ openLimit ≫ pushLimit ≫ lim(scalarComposite), and scalarComposite = derived e₀ followed
    by d. Exactly the node's order.
13. The scalar comparisons identify Rp_* Res_n with Res_n Rp_{*,A_n} and j_! Res_n with
    Res_n j_{!,A_n}: `ScalarComparison.open_normalized` and `push_normalized` against
    `ordinaryOpenScalar`/`ordinaryPushScalar` (the recorded `openRestrictionMap` and
    `proEtaleRingRestrictionDirectImage`); `derived_normalized` gives the derived push.
    Correct.
14. n-th projection = Rp_*j_!(q_n) followed by the scalar comparisons: the last clause,
    with `quotientAugmentation = η ≫ π_n` and `finiteScalarComposite`. I checked every
    source and target. Correct.
15. All quotient transitions preserved; no constructibility, smoothness, output
    normalization or cone choice: all scalar data are maps of strict systems; no such
    hypothesis appears. Correct.

Existential data and how each is pinned (so none is an arbitrary choice):
- `h : ScalarSquares` is a Prop.
- `a : LimitPresentation`: `ordinaryEvaluation` is fixed on local tensor generators.
  `evaluation` is fixed by the universal counit ε of the left-derived model, on every complex.
  `unit_projection` fixes every projection of the unit. Only the r ⊣ L adjunction is left,
  up to an automorphism of r that is the identity on each evaluation. As in item 9, this
  does not affect which inputs are admitted or whether the comparison is invertible.
- `v : Evaluation`: identity on sections (HEq), which is possible because both
  `D.equivalence` and `b.realization` are section-normalized.
- `s : ScalarComparison`: the two ordinary comparisons are fixed componentwise. The derived
  push comparison is fixed by the two composition units on all complexes.
- `w`: fixed on K-injective towers by `IsFixedPushEvaluation`.

The added projection clauses for `openLimit` and `pushLimit` are true. Here is why. The
projection `coefficientConstantTowerProjection` is the unique map that equals `lim.π n` on
K-injective towers. On such towers that is the n-th evaluation of the counit of
`cbcRealizationLimitAdj`, and both clauses are mates of identity constant squares.

Edge cases: M = 0; empty X, X̄ or Y; j = id and p = id; j clopen; level n = 0 (quotient
ℓ^1); the identity transition; unbounded M with r_X M ∈ D^{≥k} for any k ∈ ℤ. None is
excluded. Universes: the schemes and E share u, which the recorded tower and shriek
interfaces force. autoImplicit is off, and no variable is unbound.

Searches (in other words than the worker's): `rg` in side-live `lean/Sheaf` for
`PurCompactSupport.image`, `IsComplete` (DerivedCompleteOnSlices, owner
def-weil-derived-complete), `IntegralDirectImageTower` (the landed downstream citer) and
`cbcRealizationLimitMap`. None states this comparison. The item is not live. The new
node is not live, and no parallel node has the same id.

Records: the item differs from side-live only in `lean` and in `stmt_deps`, where the new
definition node was added. Both `lean.statement` fields are verbatim in their files, and
the declaration lists equal the files (6 and 51 declarations). No stmt_dep of the new
node reaches the item, the new node, det-sp-integral-direct-image-tower or the unit, so
there is no cycle. There is one sorry, the theorem's. Every definition has real data.
Every declaration has a source and `(blueprint: …)` docstring. Lines are at most 100
characters.

Mismatches in the Lean: none. Advisory notes for the maintainer:
(i) `image` could be written as an abbrev of `PurCompactSupport.image`. It is already the
same term.
(ii) Derived completeness is rendered by the node's own definition, the unit. The
recorded `IsDerivedComplete` and `IntegralOnSlice.IsComplete` use other presentations.
(iii) The new node cites the statement nodes det-sp-normalized-equivalence,
det-sp-tower-shriek-levels, lem-cbc-complete-proetale-strict-tower-realization and
lem-weil-pbc-ring-sheaf-change-adjunction for the constructed data they own. Some def
owners are not cited: def-coef-ringed-sequence-site, def-weil-pbc-proetale-operations,
def-weil-extension-by-zero, def-weil-pbc-system-scalar-model, sk-def-sp-normalized-towers
and def-cbc-strict-constant-tower-operations.
(iv) Both modules import the proof-dependency modules for stage 3.

Changed: this section only.

## New nodes

`def-sp-complete-compactification-limit-comparison` defines the ordered comparison word
and its normalized presentation interfaces in
`Sheaf.Paper.CompleteCompactificationLimitSupport`. Its main declaration is `comparison`.
The source is current blueprint paragraph (2), expanded exactly in the item's existing
five-step proof. The source integral ring, strict reduction, exact forgetting, fixed-ring
limit and simultaneous operations are all reused. The new parts are the normalization
interface and the actual natural-transformation word, which were not a usable recorded
notion. Searches in Mathlib, upstream Lean, project Lean and the DAG found no exact match;
their results are in `mathlib_searches`. This definition asserts no existence or
invertibility: the original item's theorem supplies them. All data are real constructions;
only the owning theorem postpones a proof.
