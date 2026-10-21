## Worker report

Module: `Sheaf.Paper.ClosedTestDerivedExchangeModel`.
Main declaration:
`AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.closed_test_derived_exchange_model`.
This is a stage-2 statement delivery, not a proof delivery. All five postponed
statements have `sorry` proofs and source/proof docstrings. All helper definitions
contain real data. The four public cache instances merely name the existing
condensed/pro-etale monoidal structures, internal-module abelian structure,
and additivity of the recorded terminal-object sections functor;
their bodies are `inferInstance`, so they change no mathematical data. They specialize existing module pullback, derived pushforward,
sections, adjunction, pullback universal property, and coefficient functors.
The section functor is the landed definition node
`def-sfb-condensed-module-sections`, with existing declaration
`AlgebraicGeometry.ProEtale.condensedModuleSections`. The duplicate new node
`def-sfb-condensed-module-global-sections` from the returned packet is dropped.
The existing landed node `def-weil-pbc-adjunction-square-exchange` records the
specified mate. Neither depends on this item. No Lean declaration is copied.

The previous worker's stale-assignment diagnosis concerned the reviewed NK stage-1
split. That node has no Lean record on the read base; it is the statement formalized
here. Its mathematical statement, proof and existing dependencies are preserved.

### Hypotheses and clauses

* A commutative condensed ring is the underlying sheaf `Λ` with `[MonObj Λ]`
  and `[IsCommMonObj Λ]`. This is the unbundled encoding of the recorded
  `Profinite.CondensedRing`; it includes every condensed ring, without a
  topological presentation. `condensedRingObj Λ Y` is exactly the recorded
  pulled-back coefficient ring, and `Mod` is Mathlib's internal module category.
* `A : Type u`, `[CommRing A]`, `I : Ideal A`, `X : Scheme.{u}`, `[IsAffine X]`
  and `f : X ⟶ Spec (.of A)` encode an arbitrary map of affine schemes.
  `closedMap A I` is the actual quotient-induced closed immersion. No finite
  presentation, integrality, noetherianity or coefficient flatness is assumed.
* `h`, `fZ` and `w : IsPullback h fZ f (closedMap A I)` retain the specified
  cartesian square, including arbitrary models of its pullback. The two tests
  are the existing `Scheme.AffineProEt.closedSiteLift A I` applied to
  `V : (Spec (.of (A ⧸ I))).AffineProEt` and V itself. The two
  `IsWContractibleRing Γ(-, ⊤)` instances are precisely the two geometric
  weak-contractibility hypotheses, not contractibility of a coefficient ring.
* `pullback f W.hom` is T. `pullback fZ V.hom` is T0, canonically the same
  fibre product as X ×_U V via w. `testMap` is the actual induced closed
  inclusion, defined by `pullback.lift` from h and `closedSiteLiftInclusion`.
  The coefficient identification on T0 is `pullComp` for its projection and h.
* `DerivedCategory.Plus.ι` includes the full bounded-below subcategory in the
  ordinary unbounded derived category. The statement quantifies over this full
  subcategory and uses `K.obj` in the ordinary unbounded right-derived functor.
  It does not replace the derived category by individual cohomology groups.
* `sectionsOver Λ b` is exact pullback along b followed by the right-derived
  existing section functor. For the pro-etale test maps b this is the localized
  RΓ(b,-) (Stacks 0D6F). The first existential natural isomorphism `eLeft`
  is exactly RΓ(V,s*Rf*K) ≅ RΓ(T,K|T). Its normalization says that composing
  the actual closed-site restriction `closedComparison` with eLeft is the
  ordinary Leray section comparison on W. The closed comparison is separately
  asserted invertible here, so this determines eLeft canonically.
* The second existential natural isomorphism `eRight` is
  RΓ(V,RfZ*h*K) ≅ RΓ(T0,K|T0). Its hom is exactly the canonical
  `sectionComparison` for the test pullback, whiskered with h*. Thus neither
  isomorphism is an arbitrary unrelated identification of derived objects.
* `exchange` applies the recorded `Adjunction.squareExchange` to the derived
  adjunctions and the canonical comparison `square`. This is the adjunct of
  the prescribed inverse-image comparison followed by the pulled-back counit.
  The last equality in the main theorem says that its evaluated natural
  transformation, followed by eRight, is eLeft followed by `testRestriction`.
* `restriction` is the actual derived adjunction unit followed by
  `pushDerivedSectionsIso`. That latter comparison is obtained from the
  ordinary section identity `pushSectionsIso` by the existing K-injective
  composition interface. `testRestriction` uses this canonical restriction
  on the actual map `testMap` and the canonical target coefficient comparison.
  Neither the restriction nor exchange is asserted invertible.
* Naturality in K is built into the natural isomorphisms on the full Plus
  subcategory and the equality of natural transformations. The auxiliary
  theorem `closed_test_test_naturality` gives both Leray comparisons' naturality
  and the closed-site comparison's naturality for every admissible test map r,
  using the actual map of the recorded closed-site lift functor.
* `section_comparison_base_change_naturality` supplies the commutative cube
  equation for localization/base change; all six cartesian faces are retained.
  `derived_restriction_localization` supplies the unit/composition equation for
  restriction itself. The hypotheses `WeaklyEtale` are the small pro-etale-site
  convention (and include isomorphisms). These equations apply to the specified
  affine square via the canonical test pullbacks and composition comparisons.
* The coefficient section takes an arbitrary monoid morphism c : Λ → Λ′ with
  both coefficients commutative, and defines exact derived restriction
  `restrict c X` from the existing `Mod.comap`. `restrictPush` is the canonical
  right-derived comparison induced by `CondensedRing.comapLowerStarIso`, in
  the direction Rf′ then Res → Res then Rf. It uses `rightDerivedPullback`
  and the exact postcomposition comparison, without assuming comap preserves
  injectives or that this comparison is an isomorphism.
* `restrictSections` uses the literal ordinary underlying section identity.
  `restrictSectionsOver` combines it with the existing
  `CondensedRing.derivedComapUpperStarIso`. The three predicates
  `CoefficientSectionComparison`, `CoefficientClosedComparison` and
  `CoefficientRestriction` spell out the commutative squares rather than
  asserting an unspecified compatibility.
* `closed_test_coefficient_naturality` quantifies over both bounded-below K
  and N and the actual supplied morphism `φ : K.obj ⟶ (restrict c X).obj N.obj`.
  It asserts the two section squares, the closed comparison square, the test
  restriction square, and naturality at φ. Together with the main theorem's
  normalization these give the displayed coefficient comparison squares.
  `scalarUnit` is the actual degree-zero ordinary `extendRestrictAdjunction`
  unit transported through the existing single-functor/comap comparison.
  Thus the ordinary x ↦ 1 ⊗ x case is covered without derived tensor or a
  flatness hypothesis.

### Dependency declarations used

* `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` (unbundled
  input as above); also imported publicly through the locality module.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.condensedRingObj`, `coefficientMap`, and their
  monoid/commutativity instances. These are the actual p* coefficients.
* `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and `Mod.comap`.
* `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward`, together with the exact
  upperStar/mapDerivedCategory and K-injective derived-adjunction interfaces.
* `Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality`:
  `condensed_derivedPullback_exact_symmetricMonoidal` records the exact
  inverse-image convention used here; the construction is the existing
  `CondensedRing.upperStar` followed by `mapDerivedCategory`.
* `WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift` and
  `AffineClosedSiteFunctorProperties`:
  `Scheme.AffineProEt.closedSiteLift`, `closedSiteLiftInclusion`,
  `affine_closed_site_functor_properties`. These construct W, its maps,
  and its specified pullback comparison; no substitute lift is introduced.
* `WeilConjectures.RingTheory.ProEtale.WContractible`:
  `IsWContractibleRing`. `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
  and `Sites.Proetale`: `IsClosedImmersion`, `Scheme.ProEt`, `ProEt.topology`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, its projections and `pullback.lift`.
* `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  `Mod.extendScalars`, `Mod.comap`, `Mod.extendRestrictAdjunction`.
* `Sheaf.Paper.CondensedQcqsPushforwardContinuity`:
  `ProEtale.condensedModuleSections`, the recorded declaration of
  `def-sfb-condensed-module-sections`. It forgets the module action and evaluates
  at `op (Scheme.ProEt.mk (𝟙 X))`. Its rightDerivedFunctor supplies derived
  sections. The continuity theorem is not used as a statement dependency.
* `Mathlib.CategoryTheory.Sites.GlobalSections`:
  `Sheaf.ΓNatIsoSheafSections`, together with
  `Scheme.ProEt.isTerminalMkId`. These transport
  `ProEtale.globalSectionsLowerStarIso` from the chosen right-adjoint global
  sections functor to the recorded terminal-object evaluation functor on both
  source and target. This preserves the canonical ordinary section identity.
* `Sheaf.CategoryTheory.AdjunctionSquareExchange`:
  `CategoryTheory.Adjunction.squareExchange`. The helper `exchange` is its
  canonical specialization, not a second mate construction.
* `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections`:
  `ProEtale.globalSectionsLowerStarIso`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `CondensedRing.comapLowerStarIso`, `derivedComapUpperStarIso`.
* `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`,
  `.KInjective` and `.ShortExactPullback`: `rightDerivedFunctorCompIso'`,
  `preservesKInjectiveComplexes`, `mapDerivedCategoryRightDerivedAdjunction`,
  `rightDerivedFunctorCompMapDerivedCategoryIso`, `rightDerivedPullback`.

The remaining ordinary proof-dependency imports preserve the node's stage-3 proof
plan: section-ring equivalence, closed inverse-image evaluation and its unit,
weakly-contractible exact evaluation, specialization counit/unit comparisons,
ind-etale basis, unbounded localization, normalization of derived adjunction and
composition, and ringed slice localization. They are plain imports.

### Edge cases and source checks

Read Stacks `proetale.tex`, lemma `lemma-closed-immersion-affines-apply`
(Tag 09BL), and `sites-cohomology.tex`, lemma `lemma-unbounded-cohomology-of-open`
(Tag 0D6F), together with the node's full eleven-step proof. Checked I = 0,
I = top (including the empty closed scheme), the zero ring, zero K and shifted
bounded-below complexes. There is no hidden nonempty test hypothesis, uniform
bound, coefficient discreteness or flatness condition. A nonflat coefficient
map is retained: only its right-derived comparison, not an inverse, is used.
The site keeps object universe u+1 and arrow universe u; coefficients are
Ab.{u+1}, as in the published framework. No universe equality is imposed.
No statement fault or STATEMENT-DISPUTED flag was found.

### Existing-declaration searches

* `msearch.py ... leanfinder`: “Derived base change along a closed immersion
  evaluated at weakly contractible affine pro etale test objects equals
  canonical restriction of derived sections”. Eight generic results, including
  restriction adjunction/functor and affine-limit section lemmas; no exact match.
* `msearch.py ... loogle`: `CategoryTheory.Functor.rightDerivedFunctor,
  CategoryTheory.Sheaf.Γ, CategoryTheory.TwoSquare`. Returned zero hits with
  “unknown identifier 'CategoryTheory.Functor.rightDerivedFunctor'”; this is
  recorded as an unsuccessful query, not evidence that that functor is absent.
* `msearch.py ... grep` in Mathlib CategoryTheory:
  `rightDerived.*[Ee]val|[Ee]val.*rightDerived|closedTest`: no match.
* `msearch.py ... leansearch`: “canonical derived exchange on lifted weakly
  contractible closed pro etale tests equals restriction of derived sections”.
  Eight generic results (ΓRes, sectionsEquiv, isoRestrict, Scheme.Etale,
  etalePretopology, derived-functor comparison instances and sheaf restriction);
  none states this model.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `closed.test|closedTest|ClosedTest|derivedExchange|derivedRestriction|sectionLocalization|derivedSections`
  and for the exact node id: no exact statement. The downstream integral-lisse
  closed-base-change module cannot be imported here: it consumes this very
  node. Its helper applications are not an independent prerequisite interface.
* Exact fresh declaration names searched in Mathlib, the upstream/project Lean
  sources and `dag/lean_names_upstream.json`: no collision.

### Validation

The saved packet passed the required initial `deliver2.py --no-push` at
`3bd0aced8b8`. That mechanical pass did not resolve the independent H12/H4
return. The repaired module is compiled with the prescribed `scompile.py`
wrapper against the live published library under its unchanged 60-second limit.
The final repaired module passed server compilation cleanly in 32.3 seconds,
with nice 19, two threads and the unchanged 60-second limit. The wrapper's
local attempt hit its time limit, then its built-in confirmation
compiled the identical bytes on the server. There were no errors or
non-sorry warnings in that successful compile. The required final delivery
dry run passed at `62c900283ea`, including sandbox compilation, compilation
under the actual library module name, and the maintainer's server preflight.

## Repair of return H12/H4

The immutable returned head was `790046091fff` (whose Lean was byte-identical
to `6c68d854`). The read-base item still has no Lean record, and comparison
against the current shared node shows only `stmt_deps` and `lean` differ.
The mathematical statement, proof, proof dependencies, all five theorem
clauses and their sorry proofs are preserved. The two localization signatures
replace the old sections functor with `condensedModuleSections`; the main
theorem signature itself is unchanged. The main signature in the
node remains verbatim from the file.

1. Dropped the duplicate new node
   `def-sfb-condensed-module-global-sections.json`. The packet now has only
   the item's node, the item's Lean module and this report.
2. Replaced that id in `stmt_deps` with the already landed
   `def-sfb-condensed-module-sections`. Read its full statement and existing
   Lean record: it requires only `MonObj`, evaluates the underlying abelian
   sheaf at the identity final object, and has the four underlying definition
   dependencies cited in the return. No dependency node is changed.
3. Changed the public sections import from `Sheaf.Paper.FormalClosedSupport`
   to `Sheaf.Paper.CondensedQcqsPushforwardContinuity`. Added a direct public
   import of `RightDerivedFunctor.Adjunction` for
   `Adjunction.mapDerivedCategoryRightDerivedAdjunction`, formerly exposed
   through the removed module. Every ordinary or
   derived sections expression now uses `condensedModuleSections`: this
   includes `sectionsOver`, `pushSectionsIso`, `pushDerivedSectionsIso`,
   `restriction`, `restrictionOver`, `sectionComparison`, `closedComparison`,
   `testRestriction`, `restrictSections`, `restrictSectionsOver`, and every
   explicit `rightDerivedFunctor.map` in the localization theorems.
4. Rebased `pushSectionsIso` by the canonical three-step composite: transport
   evaluation on Y back to Γ via the inverse of
   `Sheaf.ΓNatIsoSheafSections`, apply `globalSectionsLowerStarIso`, then
   transport Γ on X to evaluation via `ΓNatIsoSheafSections`. All three are
   whiskered with the actual forgetful/module-pushforward functors. This is
   the canonical section comparison, not an arbitrary choice of isomorphism.
   The derived comparison and adjunction-unit restriction are obtained from
   exactly that ordinary composite by their existing interfaces.
5. `restrictSections` remains `rightDerivedPullback (Mod.comap ...) (𝟙 _)`:
   after forgetting module actions, restriction of scalars leaves the
   terminal-object evaluation functor literally unchanged. Thus the actual
   coefficient map and the degree-zero extension unit remain covered.

Fresh source reads/searches for this repair: `rg` of `condensedModuleSections`,
`formalClosedSupportSections`, and `ΓNatIsoSheafSections` in the project and
Mathlib located the landed abbreviation at
`Sheaf/Paper/CondensedQcqsPushforwardContinuity.lean:127–135`, the comparison
at `Mathlib/CategoryTheory/Sites/GlobalSections.lean:80–82`, and the canonical
pushforward comparison in upstream `FiniteCoefficient/UpperLowerStar/GlobalSections`.
Read these complete definitions and docstrings, `CondensedRing.lowerStar`,
and `CondensedRing.comapLowerStarIso`. The new import supplies the same
site/coefficient universes as before. No new mathematical notion is introduced and no further search record or
definition node is needed. The extra cache instance `moduleSectionsAdditive`
uses `inferInstance` to name the existing composite functor's additivity; it
is listed in `lean.declarations`. Explicit site arguments avoid redundant
metavariable elaboration in the Γ/evaluation transport.

## Second reading by Q26

This is the repairing worker's self-check; no independent worker was started,
as the dispatch brief requires the maintainer's independent review.
I read the retained node and the whole Lean module, the landed sections node
and its actual abbreviation, the Mathlib Γ/evaluation comparison, and the
upstream pushforward section isomorphism. The returned defect is repaired by
using the one recorded sections notion throughout. Every other clause retains
its previously reviewed interpretation, detailed above: arbitrary commutative
condensed Λ; arbitrary affine f and ideal I; actual cartesian square and
closed-site lift; both geometric w-contractibility hypotheses; full D⁺;
the two derived natural isomorphisms and their normalization; prescribed
adjunction mate; canonical test restriction; test, square/localization and
actual-coefficient-map naturality, including the degree-zero scalar unit.
No hypothesis, axiom or invertibility assertion is added. The edge cases
I = 0, I = top, zero ring, empty scheme and zero/shifted K remain allowed:
Γ/evaluation transport only uses the identity object's terminal property,
which is valid also for the empty scheme. The site retains object universe
u+1, arrow universe u and abelian coefficients u+1. No statement correction
or dependency module is needed.
