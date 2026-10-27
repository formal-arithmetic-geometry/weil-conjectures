## Worker report

States `AlgebraicGeometry.Etale.coefficientDualizingOpenTensor` in
`Sheaf.Paper.CoefficientDualizingOpenTensor`. Its sole postponed proof is `sorry`.
`DualizingOpenTensorProperties` packages this node's conclusions; it introduces no
alternative tensor, scalar extension, constructibility or Tor-amplitude notion.
`openTensorEvaluationZero` is an actual composite of the published ordinary scalar
comparisons and the open adjunction counit. Both helpers belong to this assertion,
are listed in lean.declarations, and contain no postponed data or proofs.

This repairs the independent return on immutable delivery head `499e163e4002`.
The saved packet was retained and first dry-run against current main: preflight and
both compile passes succeeded (dry-run commit `27ced424d27`). The return nevertheless
identified a definition-ownership fault, repaired below. Against the current read
clone the item changes only `lean` and `stmt_deps`; its mathematical statement,
proof, source, split and review records are unchanged.

Hypotheses and setup, individually:

- The fixed algebraic closure of a finite field is `D : FiniteFieldDatum`; its p,
  a, q, finite base field, algebraic closure and inclusion are the existing datum.
- The coefficient prime and its distinction from the characteristic are
  `(l : ℕ) [Fact l.Prime] (_hdifferent : l ≠ D.p)`.
- The finite extension is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`.
- Positive quotient levels are `(m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)`.
  The actual rings are `ULift (Padic.coefficientExtensionRing l E n)` and the
  corresponding m-th quotient. The map is the lifted `Ideal.Quotient.factor`
  for `Ideal.pow_le_pow_right hmn`. Thus no arbitrary coefficient homomorphism
  is substituted in the theorem. The common lift implements the existing site
  size convention; it changes neither modules nor the quotient map.
- Y over k is `[Y.Over (Spec (.of D.k))]`. Its structure morphism is separated,
  locally of finite type, and quasi-compact, rendered by the three corresponding
  instance binders. Noetherian is `[IsLocallyNoetherian Y] [CompactSpace Y]`.
- The quasi-compact open immersion is `(j : U ⟶ Y) [IsOpenImmersion j]
  [QuasiCompact j]`.
- W is an object of `DerivedCategoryModule` for the n-th quotient on Y, with
  `_hW : finiteTorConstructibleEtale l E n (hm.trans hmn) Y W`. This is precisely
  the recorded bounded finite-value constructibility and finite-Tor predicate.
  In particular no flatness or finite projective dimension of B over A is assumed.
- L is the explicit term `(derivedRestriction (A := A) j).obj W`, rather than a
  free object or an unexpandable statement-local let.
- The introductory F, G, omega, epsilon and compact-support c are background
  notation in the node. They do not occur in its open comparison conclusions and
  impose no extra datum or hypothesis. Their recorded declarations were read;
  this theorem makes no choice of a compactification, exceptional functor or c.

Conclusions, individually:

- d_L is the existing B-linear isomorphism `(openScalarExtension φ j).app L`.
  Its type already supplies the isomorphism in the B-coefficient derived category;
  no arbitrary A-linear isomorphism is lifted to a purported B-map. The explicit
  identification of scalar change with restriction is the canonical
  `openScalarRestrictionMap`; the evaluation field uses `(openScalarRestrictionMap φ j).app W`
  directly, and does not use the invertibility theorem or its `asIso` wrapper.
- `evaluation` is q_L followed by `derivedExtension_B.map r_W` and the actual
  B-adjunction counit, equal to `scalarExtension.map` of the actual A-counit.
  These are the two sides of the node's equation after its stipulated pullback
  identification. Composition uses Lean's diagrammatic order.
- The prescribed q is already characterized by `OpenScalarExtensionNormalization`
  in the published scalar-coherence dependency: on every K-flat representative it
  agrees with ordinary q-zero through the fixed scalar representative maps and
  exact localization factors. This normalization is reused, rather than appended
  as a stronger global conclusion about inputs unrelated to W.
- `evaluation_before_localization` asserts equality of actual cochain morphisms
  for every K-flat P on Y representing W (`Nonempty (Q.obj P ≅ W)`). The left side is `openTensorEvaluationZero` applied
  degreewise, while the right side is the ordinary A-evaluation followed by
  ordinary scalar extension, also applied degreewise. Since B is in degree zero,
  ordinary scalar extension in each degree is the direct-sum total tensor with B.
  There is no assertion that stalk functors detect derived morphism equality.
- `bounded_constructible_A` and `bounded_constructible_B` use exactly
  `DerivedCategory.isBoundedConstructible`, for j_! L and j_! scalar(L).
- `finite_tor` supplies a common finite Tor interval for the two displayed
  extensions. The `tor_bounds` field
  quantifies over every a ≤ b and every Tor bound of L, and asserts that exact
  same interval for the A-extension and the B-extension. It tests all degree-zero
  module sheaves using the recorded `hasTorAmplitudeIn`.
- `stratifications` provides finite scheme stratifications S on U and SY on Y.
  An embedding e of their finite indices has complement exactly one index z;
  the e(i)-stratum is `j '' S.stratum i`, and the z-stratum is `(Set.range j)ᶜ`.
  On S, all degrees of both L and scalar(L) are finite locally constant; on SY,
  all degrees of both extended complexes are finite locally constant. On z,
  each of the two extended cohomology sheaves restricts to zero. Thus this is an
  extension of a finite locally closed constructibility stratification, not just
  a bare claim that some unrelated constructibility stratification exists.
  Common refinement over the finitely many nonzero degrees and both coefficients
  gives the simultaneous version; the node's proof expressly permits this.
  `Scheme.IsFiniteLocallyConstantSheaf` uses finitely generated stalks; over these
  finite rings this is equivalent to finite stalks, with the same locally constant
  module models. The bounded-constructible fields separately use the exact
  finite-value predicate recorded by the dependency.

Dependency declarations read and used:

| Node | Module and declaration/interface |
| --- | --- |
| def-kun-derived-tensor | WeilConjectures.SixFunctors.Etale.Derived.Tensor: Etale.derivedTensor |
| def-kun-tor-amplitude | Sheaf.AlgebraicGeometry.EtaleTorAmplitude: hasTorAmplitudeGE; bounded hasTorAmplitudeIn from WeilConjectures.SixFunctors.Etale.Derived.Coefficients |
| def-weil-finite-field-fiber | Sheaf.Paper.FiniteFieldFiber: WeilConjectures.FiniteFieldDatum; Padic.coefficientExtensionRing from its coefficient import |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType; QuasiCompact |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper and its IsSeparated field; only separatedness is needed here |
| def-weil-pbc-constructible-complexes | WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes: Etale.DerivedCategory.isBoundedConstructible |
| def-weil-pbc-derived-categories | WeilConjectures.AlgebraicGeometry.DerivedCategories: torsionCohomology; its public Coefficients import supplies DerivedCategoryModule |
| def-weil-pbc-extension-by-zero | WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs: openImmersionLowerShriek and openImmersionLowerShriekUpperStarAdjunction |
| lem-pur-etale-open-derived-tensor | WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection: derivedOpenImmersionLowerShriekProjectionIso; the recorded exact/scalar comparisons are used through EtaleOpenTensorDefs |
| prop-weil-pbc-inverse-image-modules-exact | WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact: etaleInverseImageModulesExact; exact constant-module inverse image here is the existing upperStar/derivedRestriction |
| lem-weil-pbc-ringed-topoi-derived-tensor-pullback | Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses: SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback; generalized K-flat/flat-term pullback and its representative square, used by the proof route |
| def-amb-etale-compact-support | WeilConjectures.SixFunctors.Etale.Derived.LowerShriek: rightDerivedLowerShriekOfCompactification, contextual only |
| lem-fix-compact-support-coefficient-change | Sheaf.Paper.EtaleCompactSupportCoefficientChange: compactSupportCoefficientComparisonPlus, contextual only |
| thm-amb-etale-exceptional-adjoint | WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint: isLeftAdjoint_rightDerivedLowerShriekOfCompactification, contextual only |
| def-weil-finite-tor-amplitude | Sheaf.Paper.FiniteTorAmplitudeSites: WeilConjectures.finiteTorConstructibleEtale |
| def-sf-etale-open-scalar-data (new existing owner) | Sheaf.SixFunctors.EtaleOpenTensorDefs: derivedRestriction, derivedExtension, openRestrictScalarsIso, openScalarRestrictionZero, openScalarExtensionZero, openDerivedRestrictScalarsIso, openScalarExtension, openScalarRestrictionMap |
| def-sp-etale-kflat-realization (landed owner) | Sheaf.SixFunctors.EtaleOpenTensorDefs: etaleKFlat |
| def-weil-pbc-witness-compatibility (landed owner) | Sheaf.Paper.WitnessCompatibility: ProEtale.pbcFixedScalarExtension; Etale.scalarExtension is its small-etale abbreviation in Sheaf.Paper.EtaleDerivedScalarTensor |
| def-sf-etale-sheaf-scalar-extension (new existing owner) | WeilConjectures.SixFunctors.ProEtale.ScalarExtension: ProEtale.etaleSheafExtendScalars and etaleSheafExtendScalarsAdjunction |
| def-constructible-finite-locally-constant | WeilConjectures.ConstructibleSheaf.Defs: Scheme.IsFiniteLocallyConstantSheaf and Scheme.Stratification |
| def-weil-pbc-etale-constructible-sheaf | WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf: Scheme.IsConstructibleEtaleModuleSheaf |

The statement dependency `lem-coef-etale-open-comparison-data` is dropped. Its
conclusion is not used in the statement: the eight constructions are plain defs,
not `.choose` constructions from its theorem. The new existing definition owners
and the two landed owners above supply the missing ownership. No declaration of
any published module is changed or copied. `def-kun-derived-tensor` continues to
supply the A-coefficient tensor; the B-coefficient scalar functor has its own owner.
No dependency modules are required. Proof imports include the recorded
open tensor and scalar coherence modules, K-flat resolutions, change of rings,
bounded-flat Tor bounds and open-extension base change. The flat constructible
model and exact-functor/cohomology nodes currently have no lean record, so there
is no corresponding module to import. This does not prevent stating the item.

Edge cases checked before writing: U empty gives zero extensions and an empty
stratification on U; U=Y permits an empty complement as a redundant final stratum
(the existing stratification definition allows empty strata). Y empty also permits
that final empty stratum. W zero works with every ordered interval. The quantifier
covers negative endpoints and a=b. The case m=n is retained as the quotient identity;
n>m includes the nonflat Z/l² to Z/l reduction. No flat coefficient-map hypothesis
is introduced. Every universe and variable is bound; all categories are the ordinary
small-etale module derived categories with their standard common u+1 coefficient lift.

Searches for an existing exact statement:

- msearch.py, leanfinder: “Derived coefficient extension commutes with etale extension
  by zero and evaluation preserving constructibility and Tor amplitude”: eight hits
  about algebraic etaleness and standard-etale presentations; no derived open result.
- msearch.py, loogle: “CategoryTheory.Adjunction.counit,
  AlgebraicGeometry.Etale.openImmersionLowerShriek”: zero hits (the latter name is
  unavailable in the Mathlib search environment).
- msearch.py, grep: “openImmersionLowerShriek|hasTorAmplitudeIn” in AlgebraicGeometry:
  zero Mathlib hits.
- rg of lean/WeilConjectures and lean/Sheaf for open tensor, scalar coherence,
  open counit and the exact node id: no existing occurrence of this node. The
  canonical maps and the general evaluation identity are already published in
  EtaleOpenTensorDefs, EtaleOpenTensor, EtaleOpenScalarCoherence and are reused.
- The live DAG contains lem-sp-etale-open-counit-flat-models, mentioned by Q34's
  stage-1 review, but it has no lean record and its mixed etale/pro-etale statement
  omits this node's stratification conclusion. It is not an exact existing Lean match.
- Direct reading of the source blueprint proof confirms the open-locality input
  and the canonical counit calculation; the retained five-step DAG proof provides
  the precise extracted tensor, finite-Tor and stratification assertions.

No STATEMENT-DISPUTED flag, statement correction, or dependency-interface fault.
The initial server compile of the complete module passed with no warnings or errors
(6.7 seconds sandbox check; 5.4 seconds library-module check).

## Second reading by NE

No second worker was started: the dispatch brief requires direct delivery and forbids
subagents. The maintainer performs the independent mathematical review. The worker's
own rereading checked the quotient-map direction n to m, the q/r/counit composition,
the actual chain-map equation, both coefficient categories in the Tor conclusions,
and the finite stratification extension and zero complement clauses against the live
node. No stage-1 statement or proof was changed. The rereading removed a redundant
global normalization conclusion, restricted the chain-map assertion to K-flat
representatives of W, and expressed finite Tor directly for the two output objects.
This keeps the conclusion scoped to the node rather than all unrelated inputs.


## Return repair

B3/H12 on head `499e163e4002`: all eight specified definitions now belong to
`def-sf-etale-open-scalar-data`, with `existing: true`, on the unchanged
`Sheaf.SixFunctors.EtaleOpenTensorDefs`. Its `lean.declarations` is exactly
`derivedRestriction`, `derivedExtension`, `openRestrictScalarsIso`,
`openScalarRestrictionZero`, `openScalarExtensionZero`,
`openDerivedRestrictScalarsIso`, `openScalarExtension`, `openScalarRestrictionMap`,
all in `AlgebraicGeometry.Etale`. The evaluation map is now the plain mate
`(openScalarRestrictionMap φ j).app W`. Its previous expression was definitionally
the same map through `asIso`; no equation or hypothesis is changed. The theorem
node `lem-coef-etale-open-comparison-data` is absent from the item's `stmt_deps`.
`etaleKFlat` is owned by the existing `def-sp-etale-kflat-realization`.
`T_Y` is the existing `Etale.scalarExtension`, transparently the small-etale
specialization of `ProEtale.pbcFixedScalarExtension`; the item now cites its landed
owner `def-weil-pbc-witness-compatibility`. Ordinary scalar extension and its actual
adjunction belong to the new existing owner
`def-sf-etale-sheaf-scalar-extension`. No theorem's isomorphism conclusion is used
as a replacement for one of these plain definitions.

The new nodes have self-contained definitions and cite exactly their ingredients.
Their records use the existing signatures verbatim, and `existing: true` means
there are no additional Lean modules to compile. Neither node owns the separate
invertibility theorem, the normalization theorems, or the already owned K-flat
predicate. The saved hypothesis/clause analysis and the reviewed edge cases above
were reread against the changed module: the sole Lean term change is the counit
comparison's r-map; all hypotheses, Tor bounds, constructibility, stratifications
and the K-flat chain equality are retained.

## New nodes

`def-sf-etale-open-scalar-data` owns the eight unchanged ordinary and exact-derived
open/scalar constructions listed in the return. Source: Stacks 03DI, 03DJ, 03EK,
03EL, 0E8I, 08FJ and 06YY, as used in the blueprint dualizing proof paragraphs 2-3.
Its ordinary scalar functor comes from the other new node, and its derived scalar
left adjoint from the existing witness-compatibility node. It states the
sectionwise scalar/restriction identity and the adjunction constructions of q-zero,
r-zero, derived q and the derived r-map, without asserting r-map invertibility.
The DAG name search found only theorem ownership of these eight definitions.
The new node records existing definitions, following the precedent of the landed
K-flat definition owner; it introduces no duplicate notion.

`def-sf-etale-sheaf-scalar-extension` owns the existing ordinary small-etale
scalar-extension functor and its specified adjunction, in the unchanged upstream
module `WeilConjectures.SixFunctors.ProEtale.ScalarExtension`. Source: Stacks 03EK.
It is sectionwise module extension followed by sheafification, with the induced
scalar adjunction, for arbitrary commutative rings and their homomorphism.
DAG searches found no definition owner: the similarly named
`def-pur-scalar-pullback-representative-data` owns a pullback comparison rather
than this functor. No module or definition is duplicated.

Searches for both new ownership records, repeated on 2026-10-22:

- msearch.py leansearch: "Canonical ordinary and derived scalar extension for
  module sheaves on small etale sites and open immersion extension by zero scalar
  comparison". Eight hits: module-category scalar extension/adjunction and
  sheafification ingredients; no exact small-etale construction.
- msearch.py loogle: "CategoryTheory.Adjunction.leftAdjointUniq,
  CategoryTheory.Sheaf". Zero hits.
- msearch.py grep: "etaleSheafExtendScalars|openScalarRestrictionMap|
  openScalarExtension|openRestrictScalarsIso". Zero Mathlib hits.
- rg on dag/nodes and both source roots finds the existing declarations at
  ScalarExtension.lean:79,85 and EtaleOpenTensorDefs.lean:48-155. Definition-only
  DAG searches show no owner for these constructions. The already owned K-flat
  predicate and derived scalar functor are reused. Blueprint search "open
  coefficient" returns zero; "scalar extension" returns 71 broader nodes, with
  no definition node for these exact constructions. The raw msearch records are
  preserved verbatim in both new nodes' `mathlib_searches`.


Repair verification (2026-10-22): `scompile.py` passes the revised main module in
both sandbox and library contexts (15.9 s and 14.7 s), with no errors or warnings.
The ownership-repaired dry run passed as `a2770760007`. A final self-check caught
and corrected a truncated `lean.statement` in the new open-map owner: the signature
now includes both functor composites and their complete type, preserving named
arguments `A := A` and `A := B`. This metadata correction does not change Lean.
The final preflight is rerun on that corrected record before delivery. JSON layout,
new-node fields, cited dependency sets, the sole expected `sorry`, explicit binders
and 100-character Lean line lengths were checked. The retained theorem signature
is unchanged, and the changed evaluation term uses precisely the requested plain
map. There is no statement correction and no unresolved return point.
