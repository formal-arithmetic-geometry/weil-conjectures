## Worker report

This stage-2 delivery states the automorphism equivalence and its specified comparisons in
`Sheaf.Paper.AutomorphismConstructibleStageEquivalence`. The statement is represented by the
family in `lean.declarations`; the primary declaration is its finite-coefficient clause.
Theorems have `sorry` proofs. All definitions and instances have actual bodies. No statement
correction or disputed statement is needed. The returned dependency ownership issues are
repaired by five existing-definition nodes described below; no Lean construction is duplicated.

### Hypotheses and coefficient conventions

- `D : FiniteFieldDatum.{u}` is the recorded finite-field datum, including its characteristic
  prime, finite field and fixed algebraic closure. `l : ℕ`, `[Fact l.Prime]` and `hl : l ≠ D.p`
  render the prime-to-characteristic convention. Infinite-stage statements use the equivalent
  instance binder `[Fact (l ≠ D.p)]`. `automorphismConstructibleStage_units` and its residue-field
  instance supply the required units; no invertibility hypothesis is added to the main statements.
- `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` are the finite
  extension. Its valuation ring, uniformizer and quotients are precisely the recorded `Padic`
  constructions. Every natural number `n` represents positive quotient exponent `n + 1`.
- `Ω : Type v`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`, `[IsAlgClosure ℚ_[l] Ω]` is the fixed algebraic
  closure. Its universe is independent of the scheme/finite-field universe. The existing small
  `AlgebraicallyClosedCoefficients.Coefficient.{u}` models represent its finite subextensions;
  a chosen finite extension may be identified with such a subextension. No new coefficient
  category or equality of site and closure universes is imposed.
- `T : Over (Spec (.of D.k))`, `[IsSeparated T.hom]`, `[LocallyOfFiniteType T.hom]`,
  `[QuasiCompact T.hom]` render separated finite type over k. `e : Aut T.left` is an automorphism
  of schemes. It is deliberately not an isomorphism in the over-category, so no k-linearity
  hypothesis is imposed.
- The helper constructions of square comparisons use schemes `X,Y`, a scheme map `f : Y ⟶ X`,
  scheme automorphisms `eX,eY`, and `h : eY.hom ≫ f = f ≫ eX.hom`. Their residue-field
  invertibility instances are derived by the preceding unit instance when specialized to the
  k-schemes of the item. These generic constructions do not require an arbitrary comparison map
  or a choice of an equivalence as input.

### Each assertion of the node

1. **Four exact coefficient-linear equivalences.** `automorphismConstructibleStage_finite`
   states constructibility in both directions, the same cohomological interval, and an exact
   equivalence whose composite with the full inclusion equals the prescribed
   `finiteDerivedPullback`. `automorphismConstructibleStage_finite_linear` spells out coefficient
   linearity in the fully faithful canonical constant-module coordinates, including all derived
   morphisms. `automorphismConstructibleStage_integral_rational` uses the prescribed
   `constructibleIntegralPullback` and `rationalDerivedPullback`, their linearity over the actual
   valuation ring and its uniformizer localization, exactness, and inverse pullback functors in
   both orders. `sfRationalCoefficientEquiv` canonically identifies that localized field with E.
   `automorphismConstructibleStage_qbar` gives the prescribed common-stage exact equivalence.
   `automorphismConstructibleStage_qbar_linear` states linearity on every common-field
   representative with every scalar of that field. Every arrow has such a representative and
   every algebraic scalar lies in a finite subextension, so this includes all Ω-scalars.
   `automorphismConstructibleStage_stageLinear` merely exposes the existing linear structure on
   the named finite-stage type; it does not introduce another scalar action.

2. **Specified inverse and shift comparisons.** `automorphismStageFiniteCancel` uses the
   recorded finite compositor and unit, with `e.inv_hom_id`. `automorphismStageIntegralCancel`
   uses `integralComparisonComposition` and `integralComparisonUnit`, constructed from the whole
   quotient diagrams and the completion unit. `automorphismConstructibleStage_inverse_comparisons`
   fixes the integral natural cancellation by those actual components, the rational one by
   localization of those components, and the algebraically closed one by the literal stage
   inclusion. Applying this statement to `e.symm` gives the other order.
   `automorphismStageIntegralShiftNormalization` fixes the restricted shift by the recorded
   signed Roos `ShiftCoordinates` and `ShiftDescent`; its rational and qbar counterparts fix their
   shifts by localization and every finite-stage inclusion. The integral and descended shift
   theorems require these predicates, exactness, and `NatTrans.CommShift` for the square maps.
   The finite restriction now names its `c : F.CommShift ℤ` and requires, for every integer
   `r` and constructible object `K`, `HEq` between the underlying component of
   `F.commShiftIso (self := c) r` and the component of
   `(finiteDerivedPullback l E n e.hom).commShiftIso r` at `K.obj`. The preceding functor
   equality fixes their endpoints; `HEq` expresses the component equality across that
   equality without selecting an arbitrary transport. Thus all four shift comparisons
   are normalized by the prescribed pullback.

3. **Every witnessing partition, same finite interval.**
   `automorphismConstructibleStage_strata` quantifies over the actual `Stratification S` and
   its locally constant restrictions and finite geometric stalks. Its conclusion uses the
   existing `S.pullback e.hom`, whose pieces are precisely the inverse images with their
   base-changed immersions, and the actual intrinsic module inverse image. Applying the exact
   derived homology comparison to each cohomology sheaf gives the stated cohomology witnesses.
   The interval clause in `automorphismConstructibleStage_finite` uses the same `Set.Icc a b`.

4. **Actual ordinary/completed agreement and completeness.**
   `automorphismConstructibleStage_completion` uses the existing
   `AlgebraicGeometry.ProEtale.inverseImageIntegralDerived` (ordinary inverse image with its
   canonical completed-ring coefficient action) and states preservation of `IsSfDerivedComplete`
   for both it and `integralDerivedPullback`. It states `IsIso` for the existing
   `inverseImagePullbackComparisonDerived`, not merely the existence of some isomorphism.
   `automorphismConstructibleStage_completion_unit` retains its factorization through the actual
   `S.adjunction.unit`, as a natural isomorphism of the ambient derived functors.

5. **Integral finite reductions, all transitions, projections and units.**
   `automorphismConstructibleStage_reduction` states an isomorphism of the entire coherent
   finite-system functors and its evaluation formula for every good representative and positive
   exponent. Since this is a morphism in the derived category of the coefficient system, it
   retains the actual quotient transitions. The right-hand side is the recorded
   `integralSystemPullbackReductionIso`: the adjoint of the defining finite Roos projection,
   transported by the actual finite pullback presentation and universal reduction counit.
   `automorphismStageIntegralFiniteReduction` composes this actual map with the recorded
   `openSquareDerivedPullbackModel`, giving exactly the node's displayed isomorphism with the
   prescribed `finiteDerivedPullback`. The completion-unit equation is retained separately in
   the preceding theorem. The final conjunct of `automorphismConstructibleStage_completion`
   preserves exactly the same uniform interval of all reductions.

6. **Natural immersion squares b and d.** `automorphismStageFiniteSquare` is the composite
   of the recorded compositors and the specified scheme equality. The integral square is the
   unique natural isomorphism whose underlying component is the analogous composite of the
   normalized integral compositors. Its definition uses that uniqueness, rather than choosing
   an arbitrary natural isomorphism. The rational square is uniquely fixed by localization of
   the integral components. The qbar square is uniquely fixed by inclusion of those rational
   components at the literal stage of every object. For the item, take `f := j` and `f := i`.
   The given relations are exactly `h` in Lean's left-to-right composition notation. These
   pullback-composition comparisons exist for any commuting scheme square, so the generic
   constructors apply in particular to both complementary immersions without replacing either
   of the specified immersion pullbacks.

7. **Full compatibility of these maps.** The finite coherence theorem gives the actual shift,
   inverse-cancellation and identity equations. The integral coherence theorem gives the
   inverse and identity equations on whole derived morphisms. `automorphismConstructibleStage_square_reduction`
   compares the reduction of the actual integral b/d with the specified square on entire
   quotient diagrams, using the actual counit-built reduction maps.
   `automorphismConstructibleStage_comparison_system` supplies simultaneous normalized
   comparison data and identifies its scalar maps with the existing
   `integralPullbackScalarComparison`. Its `IntegralComparisonRealizationCoherence` includes
   system-level and realized associativity, units, scalar units, scalar towers and rational
   scalar-composition equations. `automorphismConstructibleStage_square_scalar` is the explicit
   scalar square for b/d. The shift theorems use the canonical normalizations described above.
   Rational square components are the images of the integral components under an actual
   functor, so the integral equations rationalize. The qbar components are these same maps in
   their common finite stages; the scalar square and the unit/tower equations give coherent
   descent and preserve the equations under every enlargement. No claim that separate finite
   reductions are faithful on derived morphisms is used.

8. **Geometric Frobenius.** The recorded `FiniteFieldDatum.geometricFrobenius` has type
   `Aut (D.geometricFiber Y₀).left`, exactly the scheme-automorphism binder used here. Thus every
   assertion specializes by using `T := D.geometricFiber Y₀` and that automorphism, with no
   k-linearity condition. For immersions from a common finite-field model, the base-change
   construction `galoisMap` fixes the model coordinate; its fibre-product projection equations
   give the two required commuting relations. The same b/d constructors then apply.

### Recorded dependency declarations used

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties`: convention record: Fixes no notion of its own (its statement says so): it collects the scheme and morphism properties used throughout, each defined in the node it names, and fixes the variant meant (of finite presentation = Stacks 01TP, regular includes Noetherian, smooth = def-sbc-smooth-morphisms, constructible = def-weil-constructible-subset). A citer uses the declaration of the named node; the Mathlib facts that stand in are the matches of those nodes: closedPoints, Scheme.residueField, LocallyOfFiniteType, QuasiCompact, LocallyOfFinitePresentation, Flat, WeaklyEtale, AlgebraicGeometry.Smooth (for def-sbc-smooth-morphisms, not yet stated), IsClosedImmersion, IsImmersion, IsOpenImmersion, IsProper, Scheme.Hom.fiber, pullback (for def-pc-base-change, not yet stated), SpecToEquivOfField, IsLocallyClosed, Topology.IsConstructible. A locally closed constructible subscheme is an immersion i with IsLocallyClosed and Topology.IsConstructible of Set.range i.base..
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `lem-weil-pbc-profinite-coefficient-inverse-image`: `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`, `AlgebraicGeometry.Scheme.proEtale_profinite_coefficient_inverse_image`.
- `def-weil-finite-torsion-constructibility`: `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`, `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- `def-weil-rationalization-karoubi`: `Sheaf.Paper.SfRationalizationKaroubi`, `WeilConjectures.sfRationalConstructibleCategory`.
- `def-weil-algebraically-closed-coefficients`: `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`, `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.
- `def-weil-frobenius-detailed`: `Sheaf.AlgebraicGeometry.FrobeniusDetailed`, `WeilConjectures.FiniteFieldDatum.geometricFrobenius`.
- `lem-weil-integral-constructible-triangulated`: `Sheaf.Paper.SfIntegralConstructibleTriangulated`, `WeilConjectures.sfIntegralConstructible_isTriangulated`.
- `def-sf-integral-constructible-linear-structure`: `Sheaf.Paper.SfIntegralConstructibleLinear`,
  `WeilConjectures.sfIntegralConstructibleLinear` and `sfIntegralCoefficientLinear`.
- `def-sf-integral-comparison-system-data`: `Sheaf.Paper.IntegralPullbackComparisonRealization`,
  `WeilConjectures.IntegralComparisonSystem` and the recorded comparison constructions and predicates.
  The existence theorem remains a proof dependency; its existential is not used as a definition.
- `def-sf-integral-pullback-reduction-comparison`: `Sheaf.Paper.IntegralPullbackSystemComparison`,
  `WeilConjectures.integralSystemPullbackReductionIso`.
- `def-fd-integral-pullback-shift-coordinates`: `Sheaf.Paper.IntegralPullbackShiftCoordinates`, `WeilConjectures.IntegralCompletedComparison.ShiftCoordinates`.
- `lem-trf-open-square-exchange`: `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`, `AlgebraicGeometry.Scheme.constantOpenSquareExchange`.
- `def-weil-inverse-image-pullback-comparison`: `Sheaf.Paper.InverseImagePullbackComparisonDerived`,
  `AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived`. The normalization theorem
  remains a proof dependency, with a plain import.

In `Sheaf.Paper.DerivedPullbackTensorHom`, the declarations actually used are
`finiteDerivedPullback`, `constructibleIntegralPullback`, `rationalDerivedPullback`,
`commonStageDerivedPullback`, `integralPullbackScalarComparison`,
`commonStagePullbackObject`, and `commonStagePullbackComparison`. The record's primary
internal-Hom declaration is not substituted for any of these functors. The finite
realization coordinates use `sfIntrinsicModuleEquivalence`; the same-interval clause
uses `proEtaleCohomologicalSupport`. The comparison-system module supplies
`IntegralComparisonSystem`, `integralComparisonComposition`, `integralComparisonUnit`,
`integralComparisonScalar`, `integralComparisonPullbackCounit`, and their named laws.
The whole-system reduction module supplies `integralSystemPullbackReductionIso`.

- `lemma-constructible-pullback-stratification`: the recorded, sorry-free
  `AlgebraicGeometry.Scheme.Stratification.pullback` in
  `WeilConjectures.ConstructibleSheaf.Pullback` (the exact partition constructor used here).

The statement now cites the five new definition-owner records and the existing definition
nodes for sequence systems, the ringed sequence site, cohomological support, inverse image,
pro-etale operations, extension by zero and the actual completion comparison. The passed
triangulated-category, unique open-square model and stratification-pullback dependencies are
retained. The theorem modules continue to supply their existing definitions through public
imports; the new records distinguish those definitions from theorems about them. No existing
dependency node is modified.
The source imports the recorded proof-dependency modules when they have published modules;
proof dependencies whose statements have not yet landed remain DAG proof dependencies.

### Edge cases checked

- Positive exponents are `n + 1`; exponent zero, whose quotient is the zero ring, is never used.
- Zero complexes and the empty scheme are permitted. Empty witnessing data are treated exactly
  as in the recorded constructibility definition; the assertion about a given stratification
  is pointwise and does not invent a nonempty stratum. Empty cohomological intervals mean zero
  cohomology and are preserved too.
- The prime-to-characteristic condition is necessary and retained. No conclusion for l = p
  is silently included. The units are derived from k's characteristic and the structure map.
- Identity automorphisms and inverse automorphisms use the actual unit/composition maps.
  The inverse-square equality is stated separately and used with `eX.symm,eY.symm`.
- Scheme automorphisms that act on the ground field are included: `Aut T.left` imposes no
  over-k condition. This is necessary for geometric Frobenius.
- Scalar identity embeddings and repeated fields are included in the normalized comparison
  system; its scalar-unit and tower laws retain them. General algebraic closures have an
  independent universe, with the existing small coefficient models used at finite stages.
- No boundedness hypothesis on the ambient completion comparison is added. Constructibility
  and one uniform interval are used only where the actual constructible categories require them.
- No individual-level joint faithfulness, etale-origin witness, perfectness or Karoubi
  completion is assumed. The whole-system comparisons retain all transition information.

### Searches before introducing declarations

- `msearch.py ... leanfinder "Scheme automorphism pullback equivalence bounded constructible
  derived categories finite integral rational algebraically closed coefficients"`: eight
  unrelated matches, including scheme carrier pullback and abstract descent; no exact theorem.
- `msearch.py ... leansearch "automorphism pullback constructible derived category equivalence"`:
  eight matches (categorical pullbacks, over-category pullback, descent equivalences,
  `Scheme.Modules.pullbackCongr` and fully faithful automorphism identities), none about the
  four prescribed constructible coefficient stages.
- `msearch.py ... loogle "CategoryTheory.Functor.IsEquivalence,
  CategoryTheory.Functor.IsTriangulated"`: zero matches.
- `msearch.py ... grep "automorphism.*[Cc]onstructible|[Cc]onstructible.*[Ee]quivalence"
  AlgebraicGeometry`: no Mathlib match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and these automorphism /
  constructible / equivalence patterns: no exact four-stage statement. Existing lisse
  automorphism and finite clopen decomposition results concern narrower categories;
  the completion-unit automorphism result concerns only its particular ambient comparison.
- Further source searches located and reused `sfIntrinsicDerivedPullbackComp`,
  `sfIntrinsicDerivedPullbackId`, `openSquareDerivedPullbackModel`, the actual integral
  comparison system, and the signed shift coordinates. No private copies of these notions
  were introduced. The square constructors are automorphism specializations and normalized
  integral/rational/common-stage lifts of these existing maps.
- `rg` in `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf` for the chosen
  declaration prefixes `automorphismConstructibleStage_` and `automorphismStage`: no collisions.

### Validation

All compilation is through the prescribed `scompile.py`, against the published server build.
The module binds all variables and universes explicitly and disables automatic implicits.
All theorem proofs are `sorry`; definitions contain the actual prescribed constructions or
choices from componentwise uniqueness statements. The file is checked without linter
suppressions, and the final delivery is subjected to the prescribed `deliver2.py` dry run.

The final elaboration section locally treats the recorded pullback constructions as
irreducible, following the published system-comparison module's technique. This avoids
unfolding their large construction data while checking shift structures. It changes no
statement, mathematical construction, global instance or axiom.

The saved packet first passed the required dry run at `05877c60e11`. A subsequent self-check
against the independent return found that this saved packet still needed the ownership and
finite-shift repairs below. The item copy has been refreshed from current main so that the
stage-1 re-split note and audit fields are retained. Only `lean` and added `stmt_deps` differ
from current main; the natural-language statement and proof plan are unchanged.


## Repair of the independent return at 796b8b95f9a9

1. **H2/H4, definitions in theorem modules.** Added five `existing: true` definition nodes,
   each bound to the actual definitions in its published module, with no new Lean declarations.
   Replaced the statement dependencies on the realization, system-comparison and linearity
   theorems by these owners. Also cited the previously uncited reduction and finite-system
   definitions through their new owners. `IntegralComparisonSystem` and its predicates are
   used as definitions; this item does not obtain them from an unused existential theorem.
2. **Spurious normalization statement dependency.** Replaced the added statement dependency
   on `lem-weil-isomorphism-derived-pullback-comparison-normalization` by
   `def-weil-inverse-image-pullback-comparison`, owner of the morphism actually used.
   The normalization theorem remains in the original proof plan and is now a plain import.
3. **H3, finite shift normalization.** The primary finite theorem now requires componentwise
   agreement of the restricted `CommShift` with `finiteDerivedPullback.commShiftIso` for
   every shift and object, in addition to its functor/inclusion equality and triangulatedness.
   This repairs the free existential while preserving the finite equivalence assertion.
4. **Advisory definition dependencies.** Added all six named existing definition nodes:
   `def-trf-integral-comparison-sequence-systems`, `def-coef-ringed-sequence-site`,
   `def-weil-cohomological-support`, `def-weil-proetale-inverse-image`,
   `def-weil-pbc-proetale-operations`, `def-weil-extension-by-zero`.
5. **Passed points retained.** The Prop-valued triangulation instances, the unique chosen
   `openSquareDerivedPullbackModel`, and `Stratification.pullback` retain their original
   owner nodes. The independent-universe algebraic closure, unrestricted scheme automorphism,
   positive exponents, pinned square maps and all interval/completion clauses are retained.
   The released stage-1 re-split note keeps this statement and needs no stage-2 correction.

## New nodes

All five nodes have `existing: true`, so their modules remain the published ones. Each has
its own self-contained definition statement, source, complete declaration list and verbatim
primary signature. The searches cover LeanSearch, LeanFinder, Mathlib grep, project-source
and DAG searches and the current blueprint. Actual logged query results are stored in each
node. The rate-limited additional LeanSearch query is recorded here as unavailable, not as
absence of a match; the successful subsequent query returned `DerivedCategory.instLinear`
and `CategoryTheory.Linear.fullSubcategory`, both already used by the specialized instance.
No matching definition-owner node was found; the former records were theorem owners.

- `def-sf-integral-comparison-system-data`: simultaneous normalized realization data, the
  counit-built composition, unit and scalar maps, and the exact composition/coherence
  predicates in `Sheaf.Paper.IntegralPullbackComparisonRealization`. Data are families over
  all finite coefficient fields and embeddings. Effectivity is part of the data, not a new
  theorem asserted here. The predicates retain whole-system and realized equations, ordinary
  unit/completion normalization, rational scalar composition and all identity/tower cases.
  This extends the existing model definition node to the simultaneous data and its maps.
- `def-sf-integral-pullback-reduction-comparison`: the existing
  `integralSystemPullbackReductionIso` in `Sheaf.Paper.IntegralPullbackSystemComparison`.
  Its binders retain every good representative, every identification with the input derived
  object and every exponent `n+1`. Its first map is the actual Roos-projection adjunct; the
  other factors only transport the finite pullback presentation and reduction of the input.
- `def-sf-integral-constructible-linear-structure`: the existing ambient and inherited
  constant-section `Linear` instances in `Sheaf.Paper.SfIntegralConstructibleLinear`.
  The full-subcategory Hom modules use precisely the ambient scalar action. This node does
  not substitute the statement that some chosen functor is linear for the action itself.
- `def-sf-integral-system-reduction`: positive quotient rings, their actual transitions,
  coherent reduction and evaluation in `Sheaf.Paper.IntegralSystemReductionFullyFaithful`.
  The reduction is inclusion followed by the canonical coefficient-system calculus, and its
  evaluation is the whiskered specified calculus comparison. Full faithfulness is not part
  of this definition and is not an extra hypothesis of the item.
- `def-sf-finite-system-derived-pullback`: the ringed-system categories, evaluation,
  whole-system pullback, its derived functor, compositor and evaluation isomorphism in
  `Sheaf.Paper.FiniteSystemPullbackCoherence`. These are ordinary derived categories of
  strict systems, not diagrams of separate derived objects. Unit generators fix the
  evaluation map; exact termwise localization fixes the derived maps.

The defining source is the current blueprint's Weil-structures paragraph, read again for
this repair, together with the recorded Stacks/coefficient-calculus constructions named in
these definitions. The diagram and scalar maps retain their existing coefficient universes;
none of the repairs equates previously independent universes. Zero objects, empty schemes,
identity scheme maps, identity scalar embeddings and repeated fields remain allowed.


### Repair validation

The shift-normalized module compiled cleanly through `scompile.py` in both sandbox and
library modes (40.6 s and 48.6 s). After explicit imports of the added definition dependencies,
the delivery wrapper also compiled the module and all existing-definition declaration probes
and passed the server preflight (dry run `ef2d6c2669a`). The final self-check corrected one
metadata signature extraction at the internal `(C := ...)` named argument, preserving the
complete `integralSystemPullbackReductionIso` signature verbatim. All new signatures are now
complete, and each logged blueprint search is recorded separately. The final packet is run
through the prescribed dry run again before delivery.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
