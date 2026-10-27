## Worker report

Item: `lem-pod-reindexing-hom-coefficient-descent`; group Q99; stage 2.
Module: `Sheaf.Paper.PodReindexingHomCoefficientDescent`.
Namespace: `WeilConjectures.PodCoefficientDescent`.
The node statement is unchanged. Its clauses are separate public declarations, all
listed in `lean.declarations`; `common_comparison_existsUnique` is the final descent
statement. Every postponed result has a named theorem, source and proof plan.
Definitions contain real constructions or the choice from a stated uniqueness
characterization of the precise arrow/structure being defined. There are no new
independent notions requiring definition nodes and no dependency replacements.

### Hypotheses and coefficient objects

* `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
  `[FiniteDimensional ℚ_[l] E]` give exactly the prime and finite coefficient field.
  All integral objects use `Padic.coefficientExtensionIntegers l E` and its recorded
  uniformizer, not a second valuation-ring construction.
* `integralTowerModules l E W` is the recorded module category on the completed
  coefficient sheaf. `completedIntegralCommRingSheafUnrestricted` is the completion
  of the specified quotient system; its quotient indexing uses `n + 1` for the
  positive exponents. No uniformizer in L is identified with one in E.
* `X Y : Scheme.{u}`, `g : X ⟶ Y`, `[IsIso g]` give the scheme isomorphism.
  `[∀ x : X, Invertible (l : X.residueField x)]` and the corresponding Y binder
  express exactly invertibility of l on the two schemes. There is no finite-type,
  finite-field-base, smoothness or properness assumption.
* The ordinary functor is the recorded `podOrdinaryReindex`. Its coefficient map
  and `PodCompletionReindex` are normalized through all quotient projections.
  `IsIntegralNormalized` relates this exact functor to the specified derived
  pullback using `podOrdinaryToCompleted`; it does not postulate another pullback.
* `L : Type u` with the same finite-Q_l-field instances and `ι : E →ₐ[ℚ_[l]] L`
  expresses the finite extension. A field algebra hom is injective automatically.
  `L'` and `j : L →ₐ[ℚ_[l]] L'` express the full tower.
* Ambient `M N : DerivedCategory (integralTowerModules l E W)` are unrestricted
  unbounded objects. Only the representative formula names K-flat/flat-term and
  K-injective resolutions; these are resolution data, not assumptions on M or N.
* Complete constructible input is exactly
  `(constructibleIntegralHomPairs l E W).FullSubcategory`. Rational and common
  inputs use the corresponding recorded Hom-pair predicates. These predicates
  retain constructibility of the Hom output; no perfectness is substituted.
* Common coefficients have `Ω : Type v`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`,
  `[IsAlgClosure ℚ_[l] Ω]`, independently of the scheme universe u. The small
  pro-etale category has object universe u+1 and morphism universe u. Explicit
  universes in `ScalarDerivedPair` and `RingedFiniteFreeBasisCoordinates` preserve
  that distinction; no extra universe equality is imposed on a dependency.

### Clause correspondence

1. `ambient_scalar` asserts `IsIso (scalarHomOrdinary ...)` for every ambient M,N.
   Its second conjunct is the equality of the inverse closed transpose with
   extended ordinary evaluation, preceded by `scalarClosedTensor.inv`. This fixes
   the actual evaluation-normalized arrow, rather than a chosen isomorphism.
   `scalarHomOrdinary` has no basis parameter, proving that the arrow being
   discussed is independent of every temporary basis.
2. `ambient_coordinates` quantifies over every finite rank and every actual sheaf
   basis isomorphism. It supplies the derived scalar adjunction on the specified
   ordinary functor. Its `β` is fixed by the displayed inverse-transpose formula
   with that adjunction's unit/counit and S-evaluation. BOTH `aH` and `aN` satisfy
   `RingedFiniteFreeBasisCoordinates`, and each `biproduct.ι` satisfies the
   displayed equation after `aH`, restriction of gamma and β. Thus it is exactly
   the finite-biproduct comparison, with neither basis map manufactured using
   invertibility of gamma. Finite biproducts are inferred from the existing
   pretriangulated derived category; no added biproduct hypothesis remains.
3. `ambient_scalar_chain` spells out evaluation on every sheafified homogeneous
   pure-tensor summand of the total Hom model. Its scalar is `s * b`, and its
   target is the SAME `specifiedHomResolutionUnit` augmentation. The second
   conjunct identifies the localization of that very chain map with
   `scalarHomOrdinary`. Thus `(f tensor s)(x tensor t) = f(x) tensor st` is a
   formula for actual representative maps, not a claim that every derived
   morphism is a section. Arbitrary degrees are quantified and the scalars have
   degree zero.
4. `ambient_reindex_scalar` gives the two scalar/reindexing routes, using the
   specified `PodReindexCoefficientTransition.derived` and the actual ambient
   `PodCompletedReflection.homComparison` at E and L. Its normalized transition
   laws fix the tensor and coefficient maps; equality is in D(S_X).
5. `ambient_tower_unit` gives the identity-extension equation under
   `integralOrdinaryDerivedScalarUnit` and the tower equation under
   `integralOrdinaryDerivedScalarComp`. Neither tameness nor unramifiedness nor
   Tor-amplitude appears. The existing `finiteFreeCompletedScalarComparison`
   identifies ordinary extension with completed extension on complete inputs;
   `specifiedHomScalarEvaluation_arbitraryScheme` pins the completed Hom
   comparison to this SAME gamma via the three completion maps. These imported
   clauses are used, not restated with an arbitrary operation comparison.
6. `integral_pair_permitted` and `integralPair` give the exact integral domain and
   its full arrow functor. `integral_comparison_existsUnique` fixes its natural
   isomorphism by `IsIntegralNormalized`: the κ_H/κ_M/κ_N square with the recorded
   ambient comparison. `integral_existsUnique` removes the choice of normalized
   model, and `integralComparison` chooses this uniquely determined map.
   `integral_evaluation_transposition` explicitly gives completed evaluation and
   transposition with `canonicalIntegralPullbackTensor`.
7. `rational_pair_permitted` and `rationalPair` retain the same object domain and
   ALL localized arrows. `IsRationalNormalized` fixes both forward AND inverse
   components to their raw localizations. `rational_comparison_existsUnique`
   and `rationalComparison` consequently descend this exact integral isomorphism.
   `rational_naturality` quantifies over arbitrary rational arrows in the two
   variables, with inverse first-variable variance.
8. `rational_transpose_existsUnique` is a linear equivalence over
   `Localization.Away (Padic.coefficientExtensionUniformizer l E)`. Its formula
   on every pure tensor is scalar times `integralTranspose`; linearity extends it
   to every finite sum. `rationalEvaluation` is inverse transpose of identity.
   `rational_evaluation_transposition` gives evaluation and transposition for
   EVERY localized input b. The recorded rational tensor/Hom operation formulas
   multiply two scalar factors; consequently naturality/evaluation on
   `sum a_i tensor lambda_i`, `sum b_j tensor nu_j` use exactly
   `lambda_i * nu_j`, not a restriction to integral arrows.
9. `shifted_pair_permitted`, `shiftedPair`, `integral_signedShift_existsUnique`
   restrict the actual `PodReindexingCoherence.signedShift`. The signed shift is
   not replaced by an arbitrary iso. `rational_signedShift_existsUnique`
   localizes its actual forward arrow and hence its inverse. Both integers a,b
   are arbitrary. `rational_pullbackShift_existsUnique` fixes the pullback shift
   by termwise reindexing, κ and localization. `rational_signed_shifts` is the
   explicit two-input shift square with these exact maps. `rational_composition`
   uses the recorded `pullbackTensorRationalComposition` on both inputs and Hom.
10. `integral_scalar` and `rational_scalar` give the finite scalar square for the
    descended comparison using precisely `integralHomScalarComparison`,
    `integralPullbackScalarComparison` and their recorded rational versions.
    The inverse-first/direct-second Hom transport is explicit. These formulas
    fix compatibility at every larger finite coefficient field, rather than
    merely existence of some compatible comparison family.
11. `commonPullback`, `commonHom`, `commonTensor` are equality-only `copyObj`
    presentations of the RECORDED functors. Their chosen maps remain those
    functors' maps transported by object equality. This permits literal
    `toStage` formulas without altering any operation or normalizing it anew.
    `common_pair_permitted` and `commonPair` provide its exact permitted domain.
12. `IsCommonNormalized` quantifies over EVERY permitted P, EVERY finite field L
    and EVERY set of indicated stage bounds. It represents the component by
    `ofHom` of the rational comparison conjugated by the existing pullback and
    Hom comparisons, including both input variances. Thus no representative or
    sufficiently-large-stage exception is omitted. `common_comparison_existsUnique`
    gives the unique NATURAL ISOMORPHISM with these representatives, and
    `commonComparison` is that map. Naturality includes arbitrary quotient-class
    arrows; its inverse equations are actual NatIso equations.
13. `common_evaluation_existsUnique` prescribes evaluation at EVERY larger field,
    with `commonStageTensorComparison` and `commonStageHomComparison` before
    rational evaluation. `commonEvaluation` chooses this uniquely fixed map.
    `common_tensorComparison_existsUnique` and `commonTensorComparison` transport
    the actual `canonicalCommonStagePullbackTensor` by equality only;
    `common_evaluation` uses this canonical map without assuming an arbitrary μ.
    `common_transpose_existsUnique` characterizes the entire Hom equivalence by
    evaluation on every arrow. `commonTranspose` and `common_transposition`
    give its preservation on every common-stage class b.
14. `common_compositor_existsUnique` transports the recorded compositor only by
    object equality; `commonCompositor` is that unique map.
    `common_composition` gives the scheme-composition equation with it.
    `common_signedShift_images` gives both signed Hom shifts as actual classes
    at EVERY finite field, with the same localized signed arrows and prescribed
    pullback shift. The common-stage shift structure is the recorded stagewise
    one, so this states its equation for all finite representatives.
    The existing `GeneralAlgebraicallyClosedCoefficients.representatives` gives
    exactly representation and eventual equality, including equality after a
    further field. Applied to the finite diagrams above it identifies their
    classes. The functors and natural isomorphisms are defined on those quotient
    classes, so equal representatives have equal images, including their
    inverses, compositions, evaluation and transpose. No faithfulness of finite
    quotient evaluation or ad-hoc representative restriction is assumed.

`HEq` in the signatures transports only the recorded object equalities or raw
localization object formulas. It does not weaken an equation to existence of an
unrelated map. Canonical tensorators and compositors are supplied with uniqueness
and their existing-arrow characterizations before being used.

### Dependency declarations used

The original statement dependencies and their interfaces were read:

* `Sheaf.Paper.DerivedPullbackTensorHom`: `integralTowerModules`,
  `integralDerivedInternalHom`, `constructibleIntegralHomPairs`,
  `constructibleIntegralHom`, `constructibleIntegralTensor`,
  `constructibleIntegralPullback`, `rationalDerivedInternalHom`,
  `rationalDerivedTensor`, `rationalDerivedPullback`, `commonStageDerivedInternalHom`,
  `commonStageDerivedTensor`, `commonStageDerivedPullback`, their object/arrow and
  `commonStage*Comparison` characterizations.
* `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `finiteFreeCompletedScalarComparison`, `integralCompletedScalarMap`,
  `integralOrdinaryScalar`, `integralOrdinaryDerivedScalar`, `scalarCompletion`.
* `Sheaf.Paper.IntegralOperationsScalarComparisons`: `scalarHomOrdinary`,
  `scalarClosedTensor`, `integralHomScalarComparison`,
  `integralPullbackScalarComparison`, and rational versions.
* `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`:
  `CategoryTheory.scalarInternalHomAdjunction_exists`.
* `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization` and its scalar/tensor formulas.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `Stage`, `Pair`, `toStage`,
  `StageHom`, `ofHom`, `representatives`, `inclusion`, stagewise shifts.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and coefficient integer/uniformizer data.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, completed coefficient sheaves.
* `Sheaf.Paper.PodReindexingHomResolutionModel`:
  `podReindexing_hom_resolution_model`, coefficient-normalized ordinary reindexing.
* `Sheaf.Paper.PodReindexingCompletedEvaluationReflection`:
  `PodCompletedReflection.Comparison`, `homComparison`, `evaluation`, `transpose`,
  and `podReindexingCompletedEvaluationReflection`.
* Scheme-morphism properties are the recorded Mathlib conventions, with `IsIso`
  and residue-field invertibility used directly.

The repaired added statement dependencies are the already-landed
`def-pod-completion-reindex-coefficient-transition`
(`Sheaf.Paper.PodCompletionReindexCoefficientTransition`,
`PodReindexCoefficientTransition.Laws` and `.derived`) and the two existing:true
plain-definition owners in the New nodes section below. The former theorem
`lem-sf-ringed-finite-free-hom-coordinates` is a proof dependency, not the owner of
the predicate in the statement. Likewise `lem-pur-derived-pullback-tensor-iso`
is not used as the statement owner of its plain compositor definitions.
`lem-pod-specified-hom-scalar-evaluation` remains available in the original
proof dependencies; its theorem is not an added statement dependency. The
`specifiedHomResolutionUnit` appearing in the representative signature is the
existing resolution-unit definition from `SpecifiedHomScalarEvaluation`,
exposed by the imports, rather than the arbitrary-scheme theorem itself.

Available stated proof dependencies are imported with plain `import`, including
finite-free Hom/tensor, scalar tensor coherence and Hom tower, the isomorphism
K-flat model, coefficient DVR, principal Koszul replacement, exact pro-etale
products, completion exchange, ambient operation models, specified κ/α, and
isomorphism scalar extension. `Sheaf.Paper.NormalizedScalarComparisonRealization`
is absent locally and `scompile.py --source` reported it unavailable on the
server; it is proof-only and no statement here depends on that absent module.
No downstream `DerivedAutomorphismHomEvaluation` import is used: it cites this
item in its proof dependencies and would create a cycle.

### Edge cases and verification

Checked the empty scheme, zero objects and zero arrows: no nonempty-scheme or
nonzero-complex hypothesis appears. Finite rank zero in the coordinates theorem
is universally quantified (there is no such basis for a nonzero field extension,
so the premise is vacuous); positive ranks are unrestricted. Identity E=E and
arbitrary ramified towers use multiplication, never equal uniformizer powers.
Negative, zero and positive a,b are all retained in the signed formulas. The
ambient statement permits arbitrary unbounded inputs without compactness,
perfectness, completeness or constructibility. Only the stated restricted
stage uses constructible-Hom pairs. Rational arrows are arbitrary sums, and common
arrows are arbitrary quotient classes. Identity field stages and arbitrary
larger stages are included. The common coefficient universe v is independent.
No statement dispute or source correction is proposed.

All compilation used `scompile.py` on this single module in module mode. An
expanded attempt exceeded 60 seconds; making `Scheme.residueField` locally
irreducible prevents expensive failed cross-scheme instance matching without
changing any statement. The full file subsequently compiled cleanly in both
sandbox and library modes, including the final integral evaluation clause.
Only `sorry` theorem proofs remain; no data definition contains `sorry`.
All variables and universes are explicit (`autoImplicit false`), and all lines
are at most 100 characters. The delivery dry run and final delivery results are
recorded by the launcher wrapper.

### Searches

* `msearch.py ... leanfinder`: natural-language search for finite free coefficient
  extension of unbounded internal Hom, evaluation and coefficient descent.
  Eight ordinary ModuleCat/FGModuleCat results; no theorem on the actual
  completed pro-etale/rational/common-stage operation maps.
* `msearch.py ... loogle "CategoryTheory.Linear, TensorProduct.map, NatIso"`:
  no hits, with unknown `NatIso`. A follow-up
  `"scalarInternalHomAdjunction_exists, TensorProduct.map"` also returned no
  hits (the project declaration is unknown to the Mathlib index).
* `msearch.py ... grep "scalar.*[Hh]om|[Hh]om.*scalar" CategoryTheory`:
  three scalar-restriction/monoidal-module hits, not this descent statement.
* `rg` of the item id and coefficient-descent names in `lean/WeilConjectures`
  and `lean/Sheaf`: no existing exact declaration. The finite scalar,
  normalized adjunction and representative evaluation interfaces above are
  reused rather than duplicated as alternative notions.
* `rg "podReindexingHomCoefficientDescent|PodCoefficientDescent"` over
  `lean/WeilConjectures`, `lean/Sheaf`, `dag/lean_names_upstream.json`:
  no name collision. Further searches of derived category biproducts,
  common-stage comparison/shift/composition and representative equality found
  the interfaces cited above. `DerivedAutomorphismHomEvaluation` contains a
  downstream assembly of related equations, not an independent replacement
  for its own coefficient-descent prerequisite.

Source checked: the current `literature/blueprint/latest/` proof of
`prop-pod-dual-tate-data-compatibility`, Step 5, together with all fourteen
proof steps of this node. The module docstrings give the matching proof plan
for each postponed result. The node's historical source field is unchanged.


## Repair of returned delivery 2b38b2204d63

The maintainer accepted the Lean signatures and returned the added dependency
metadata under H2. Each numbered point has been repaired:

1. Removed `lem-sf-ringed-finite-free-hom-coordinates` from the additions to
   `stmt_deps`. Added `def-pod-finite-free-basis-coordinates`, an existing:true
   attachment to `CategoryTheory.RingedFiniteFreeBasisCoordinates`. Its statement
   defines the exact K-flat representative predicate, not the coordinates theorem.
2. Removed `lem-pur-derived-pullback-tensor-iso` from those additions. Added
   `def-pod-rational-common-pullback-composition`, an existing:true attachment to
   `WeilConjectures.pullbackTensorRationalComposition` and
   `WeilConjectures.pullbackTensorCommonComposition`. It defines the same
   localization and every-larger-field representatives used in the signatures.
3. Removed `lem-pod-specified-hom-scalar-evaluation` from those additions. No
   declaration of that theorem occurs in the statement. Its import continues to
   expose the existing `specifiedHomResolutionUnit` needed by the representative
   formula; importing a module does not make its theorem a statement dependency.

The sandbox item was compared field by field with current main. Only `lean` and
`stmt_deps` differed; all remaining current-main fields were retained. The Lean
module is byte-identical to the accepted Lean module of returned head
2b38b2204d63. The two new definition records and these dependency replacements
are substantive repairs; this is not an unchanged re-push. Delivery tooling
performs the authorized rebase and current-main commit construction.

## New nodes

`def-pod-finite-free-basis-coordinates` owns the existing plain predicate
`CategoryTheory.RingedFiniteFreeBasisCoordinates` in
`Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeCoordinates`. Its full source
signature and body were read. It quantifies over every K-flat representative F,
every q:QF≅X and basis index j; fixes the degreewise scalar-section formula and
its precise restriction/localization equation; and imposes no existence theorem
for a basis or Hom isomorphism. Rank zero is vacuous. The source is the current
blueprint Step 5 coefficient transport and the finite-free representative
specialization of Stacks 08J9/08JA. Existing DAG owner searches found only the
coordinates theorem, not a definition node. The nearby
`def-pur-finite-scalar-coordinate-data` constructs normalized coordinate
isomorphisms; it does not supply this generic predicate on a supplied a,E,T,ε.
LeanSearch found eight ordinary algebra/flatness results; LeanFinder found eight
basis/free-module-sheaf results; exact Mathlib grep found zero. Project grep found
this exact existing declaration, hence existing:true and no duplicate module.
All exact queries, results, dates and digests are in `mathlib_searches`.

`def-pod-rational-common-pullback-composition` owns the two existing plain
compositor definitions in `Sheaf.Paper.DerivedPullbackTensorIso`. Their complete
signatures, uniqueness specifications and bodies were read. The rational arrow
is the localization of the fixed integral compositor; the common-stage arrow
is its representative at EVERY field containing the object's stage, conjugated
by all three prescribed pullback comparisons. Its natural source/target and the
actual ofHom class map are retained. This applies to arbitrary composable scheme
morphisms with l invertible, including identity morphisms and zero/empty inputs;
it is not a theorem that pullback preserves tensor. The source is current
blueprint Step 5 transport, with the original declarations' Stacks 07A4/0941
coefficient conventions. DAG searches found the containing tensor-isomorphism
theorem only, not a definition owner for these two declarations. LeanSearch and
LeanFinder each returned eight ordinary pullback/composition results, not the
localized/common-stage normalized compositor. Exact Mathlib grep found zero;
project grep found the two existing declarations. Thus this is an existing:true
attachment with no new Lean definition. Queries/results/digests and the broad
blueprint search are retained in `mathlib_searches`.

No new Lean modules or changes to existing dependency records are needed.
The unchanged main module was recompiled through scompile.py for this repair;
the dry-run and push perform the prescribed current-main verification again.

## Second reading by Q99

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Review FIX (maintainer review of 503058d0d6bd, 2026-10-25)

- `ambient_scalar_chain` used `WeilConjectures.specifiedHomResolutionUnit`, a plain definition owned only by the theorem node `lem-zl-specified-hom-scalar-evaluation`. That node is not a statement dependency, and is not one of this item's either (delivery-errors H2). Its body is now inlined at both uses. The inlined term is the K-injective augmentation `CochainComplex.toKInjectiveResolution` of the fixed resolution, under the same Grothendieck-abelian instance, typed into `coefficientHomResolution` (owned by def-coef-hom-representative-evaluation). This is the same map, so no mathematics changes.
- The public import of `Sheaf.Paper.SpecifiedHomScalarEvaluationArbitraryScheme` is replaced by public imports of `Sheaf.Paper.CoefficientHomRepresentativeEvaluation` and `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- The fixed module compiled clean through nt_compile.py in 48.1 s.
- In `def-pod-finite-free-basis-coordinates`:
  - lean.statement is restored to the full signature. The delivered field was cut at `(R`.
  - The pure-section citation now names def-fix-ringed-scalar-extension-section, which owns `ringedFiniteFreeScalarSection`.
