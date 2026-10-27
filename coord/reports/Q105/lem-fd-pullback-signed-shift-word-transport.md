## Worker report

The delivery states `lem-fd-pullback-signed-shift-word-transport` in
`Sheaf.Paper.FdPullbackSignedShiftWordTransport`. Its three postponed declarations
are `WeilConjectures.FdSignedWord.pullbackShift`, `.roosShift`, and
`.fdPullbackSignedShiftWordTransport`. Every theorem proof is `sorry`; every
helper definition has actual data. The main theorem supplies the record
`FdSignedWord.Transport D` for the dependency's specified normalized realization
system `D`. This record is a conclusion, not an additional hypothesis.

The fields of `Transport` retain the actual operations, rather than defining an
arbitrary collection of comparisons to satisfy the conjugation formula. In
particular `pbcPrimitive` evaluates a scheme letter by
`pbcActualCompletedPull` and a scalar letter by `pbcEmbeddingAmbientTensor`;
`pbcWord` recursively composes those very functors. Primitive comparison fields
pin their arrows to the independently defined completed compositor, completed
identity, scalar/completed-pullback mate, scalar tensor associator and scalar unit.

### Hypotheses and clause-by-clause correspondence

- The prime is `(l : ℕ) [Fact l.Prime]`. Finite coefficient fields and finite
  coefficient maps use the existing `CounitRealization.Coefficient` and
  `Primitive.scalar`, with `Field`, `Algebra ℚ_[l]`, `FiniteDimensional`, and an
  actual `ℚ_[l]` algebra map. This is the existing dependency's small-model encoding
  of finite fields inside any fixed algebraic closure; a subfield inclusion is
  represented by its algebra map, including identity and composite maps. No choice
  of a new algebraic closure or field presentation is added. The statement is
  invariant under the supplied coefficient presentations and therefore needs no
  unused algebraic-closure binder. It includes every finite subfield of the fixed
  closure in the node.
- The standing scheme hypotheses are `geometry a`: `IsNoetherian a.scheme`, a
  finite bound on `topologicalKrullDim`, and `IsUnit (l : stalk x)` at every point.
  `geometric w` imposes these at every location and requires `IsIso f` for each
  scheme letter. `Location.invertible` is the dependency's residue-field encoding
  of the same invertibility condition. A scalar letter's `primitiveIso = True`
  means there is no extra scheme-map condition on a scalar letter; it is not a
  new mathematical hypothesis.
- The completed coefficients, positive quotient levels and their actual
  transitions are the dependency's `integralTowerModules`, `pbcIntegralDatum`,
  `integralOperationsPullbackTowerFunctor` and `scalarRoosBoundary`. Natural index
  `n` means positive quotient exponent `n+1`. No different coefficient ring,
  tower, transition, or product construction is introduced.
- The two presentations are `integralDerivedPullback` and
  `pbcActualCompletedPull`. The coefficient identity `I` is exactly
  `integralDetailedTransport`; its canonical shift is exposed as
  `fdSignedTransportShift`, using `(fdCoefficientTransport ...).mapDerivedCategory`.
  These are restriction along the published quotient-normalized identity.
- The ordinary pullback and the good flat-term K-flat representatives occur
  through `FdCompletedPullbackNormalization.ordinary`, `.ordinaryComputes`,
  `.tower`, `.coneCoordinates`, and `.realization`. `pullbackShift` quantifies over
  that normalized comparison `N`, so its shift square concerns the specified
  comparison and its retained representative identifications.
- The normalized rho is the existing `IntegralComparisonRoosModel.comparison.inv`,
  from the same `D`. Its `computes` condition and the dependency's
  `FdCompletedRoosNormalization.resolution` fix the K-injective formula
  `[iota]^-1[H(q)]`. `roosShift` states its shift square explicitly, with the
  canonical `DerivedCategory.Q` and total-right-derived-limit shift comparisons
  inserted in the correct order.
- The signed cone coordinates are precisely
  `IntegralCompletedComparison.ShiftCoordinates`; descent is precisely
  `IntegralCompletedComparison.ShiftDescent`. `pullbackShift` asserts both and
  then `NatTrans.CommShift N.comparison.hom ℤ` and the inverse square. These are
  the displayed ambient equation in categorical composition order. Restriction
  to the full integral categories leaves the arrows unchanged.
- `roosShift` additionally writes both coordinate equations after every product
  projection. The unshifted coordinate is unchanged, while the shifted coordinate
  is multiplied by `r.negOnePow`, i.e. `(-1)^r`, for every integer `r` and every
  degree. This is exactly the reversed `(y,x)` formula in the node.
- The normalized augmentation is the actual
  `integralComparisonLimitToRoos`; `roosShift` asserts that its shifted version
  followed by the signed map equals the canonical termwise-limit shift followed
  by the shifted augmentation. This says that every `(0,z)` is fixed. Since the
  comparison is a `CommShift`, it is natural for every strict degree-zero tower
  map; those maps act diagonally on the two cone coordinates. For the actual
  mixed scalar comparison the explicit resulting square is `Transport.actualShift`
  at `Comparison.scalarPullback`; `scalarShift` retains the normalized scalar
  representative/chi shift property.
- The primitive-map suppositions are rendered using their *specified maps*, not
  supplied arbitrary arrows: `pullback` identifies wordwise b with
  `FdCompletedPullbackNormalization.comparison`; `scalar` identifies its scalar
  counterpart with `I(chi^-1)` followed by the generator-normalized
  `FdScalarCoefficientTransport.derivedIso`. Here `chi` is the published
  `scalarCompletionIso`, the exact ordinary-derived scalar presentation of the
  same quotient/zero-coordinate completion map. The general derived tensor
  presentation in `completedScalarShiftRepresentativeProperty` has a different
  Lean functor, so its inverse is never silently composed with the exact ordinary
  functor's comparison. The existing normalized comparison for that presentation
  is used instead.
- Finite composable words, parentheses, the empty word, and all specified
  comparisons are exactly `CounitRealization.Word` and `.Comparison`; no private
  word syntax replaces them. `Word.comparison (fdCounitRealizationModels l D)`
  is the dependency's recursively counit-built r. `Transport.laws` is the
  existing `WordLaws` and `ScalarLaws` conclusion, including the entire-system
  counit and intermediate counit insertion, invertibility, parenthesization,
  uniqueness, both whiskerings and inverse transport.
- The stipulated domain is `Word.Allowed C` and
  `IsNormalizedCoefficientSequence ... C`. `Transport.domain` concludes the
  corresponding full-integral domain `input w (L C)`, including every completed
  intermediate value. It does not ask for additional normalization of intermediate
  objects; the dependency's word laws supply it.
- The identification formula is `Transport.substitution`. It reads
  `b_w ≫ actual(t) ≫ b_v.inv = I(r_w ≫ L(t) ≫ r_v.inv)`.
  `realizationIso` has hom exactly the original `Word.comparison` and obtains
  invertibility only from `WordLaws.invertible` on the stipulated domain.
  Consequently this is the node's formula `r_v^-1 L(t) r_w` and its intertwining
  with both presentations, with categorical composition written left to right.
- `nil` and `comp` fix b on the empty word and its recursive composition.
  `naturality` is naturality on the common full integral categories.
  `actualPullbackComp`, `actualPullbackUnit`, `actualScalarPullback`,
  `actualScalarComp`, and `actualScalarUnit` pin every primitive to the named
  actual PBC map. `actualComp`, `actualInverse`, `actualLeft`, and `actualRight`
  specify actual composites, inverses and both whiskerings.
- `systemPullbackShift` is the exact inverse-image shift; `systemScalarShift`
  fixes the system scalar shift through its actual universal cochain counit.
  `systemShiftComp` and `systemShiftNil` retain them for all word parentheses.
  `pullbackShift` and `scalarShift` pin the completed letters' signed descents;
  `shiftComp` and `shiftNil` specify composite and empty shifts. The PBC shifts
  `pbcWordShift` and `pbcInputShift` use its existing canonical primitive shifts.
  `realizationShift`, `wordShift`, and `actualShift` assert the three relevant
  signed shift squares for r, b, and the actual comparisons.
- The equalities of entire quotient diagrams are retained as
  `IntegralQuotientMixedCoherence` in `mixed` and transported by `coherence`.
  In particular all instances of associativity, units, equal scheme maps,
  repeated fields and successive scalar extensions supplied by the dependency
  become equalities of actual integral arrows. This uses entire-system equality,
  not joint faithfulness of finite evaluations.
- `ScalarLaws.associator` is exactly the existing `CompletedLineTensor.associator`,
  defined by ordinary tensor associativity conjugated by chi; `ScalarLaws.unit`
  is multiplication followed by completeness, including equal fields. The PBC
  versions are pinned to `pbcAmbientScalarComp` and `pbcEmbeddingAmbientUnit`.
- `constructible` records membership of actual word values in the full integral
  category. `rationalCoherence` applies the actual `pbcRationalization` to the
  corresponding full-subcategory arrows. This is raw scalar localization at
  `pbcUniformizer`, with no Karoubi completion. The comparison syntax is closed
  under inverses; `actualInverse`, `WordLaws.inverse` and `actualShift` include
  those inverse comparisons and their signed squares.
- There is no Tor-amplitude condition, finite-level flatness premise, boundedness
  condition on K-flat representatives, or invertibility assumption on strict
  degree-zero maps. The only constructibility/completeness restrictions are the
  ones explicitly stipulated for the word realizations.

### Dependency declarations and searches

Read every `stmt_deps` node, its recorded declarations or Mathlib matches, and the
source signatures/docstrings. The statement uses, through public imports:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`; `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, through the good-representative
  and normalization dependencies.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralDetailedTransport`, `integralStratifiedPerfectCharacterization` and the
  common full integral categories. `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
  supplies the original finite coefficient constructions and finiteness interface.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: the completed quotient coefficients
  and the actual small site. Object and morphism site universes remain u+1 and u.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` and
  `Sheaf.Paper.DerivedPullbackTensorHom`: `integralDerivedPullback`, its strict tower,
  its representative comparison, and `constructibleIntegralPullback`.
- `Sheaf.Paper.PbcQbarCompletedPullback`: the actual PBC completed pullback underlying
  `pbcQbarCompletedPull` at each finite stage.
- `Sheaf.CategoryTheory.StrictRoosComparison`: `strictRoosComparison`;
  `Sheaf.Paper.IntegralPullbackShiftCoordinates`: `ShiftCoordinates`, `ShiftDescent`.
- `Sheaf.Paper.FdPullbackAugmentationCounitMatching`:
  `fdCounitRealizationModels`, `FdRoosResolutionFormula`, and the matching
  normalization of the entire-system counit.
- `Sheaf.Paper.FdCompletedCompositorNormalization`:
  `FdCompletedRoosNormalization`, `FdCompletedPullbackNormalization`, and the
  primitive compositor normalization.
- `Sheaf.Paper.FdScalarPullbackRealizationIdentification`:
  `FdScalarCoefficientTransport` and the actual scalar realization maps;
  its public ordinary-scalar interface supplies `scalarCompletionIso`.
- `Sheaf.TraceFormula.CounitRealizationSubstitution`:
  `Coefficient`, `Location`, `Primitive`, `Word`, `Comparison`, `WordLaws`, `ScalarLaws`,
  the actual recursive `Word.comparison` and `counitRealizationSubstitution`.
- `Sheaf.Paper.QuotientSystemMixedCoherence`: `IntegralQuotientMixedCoherence`;
  `Sheaf.Paper.SfRationalizationKaroubi` and its PBC coefficient dependency:
  the raw rational categories and the existing `pbcRationalization`.
- Proof imports retain `StrictRoosShiftLocalization`,
  `FinitePullbackStrictTowerComparison`, `IntegralOperationsWellDefined`,
  `ProEtaleCountableProductsExact`, and `Mathlib.CategoryTheory.Localization.Predicate`.
  `FdNormalizedIntegralCompletionComparison` supplies the normalized scalar-shift
  interface. The generic right-derived shift is imported from the published
  `WeilConjectures...RightDerivedFunctor.Triangulated`, not redeclared.

Searches on 2026-10-24:

1. `msearch.py ... leanfinder "Normalized Roos comparison for completed pullbacks
   commutes with signed shifts and transports finite words of scheme pullbacks and
   coefficient scalar extension"`: eight hits, generic scheme pullback/affine
   comparison helpers. None states this normalized signed word transport.
2. `msearch.py ... loogle "CochainComplex.mappingCone.shiftIso,
   CategoryTheory.NatTrans.CommShift"`: zero hits for the combined query.
3. `msearch.py ... grep "roos.*[Ss]hift|[Ss]hift.*roos" Algebra/Homology`:
   zero Mathlib hits.
4. `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for signed shift/word names, `ShiftDescent`,
   `fd.*[Ss]hift`, and `Word.*[Ss]hift`, and literal item-id search upstream:
   no exact existing declaration. Found and read the existing shift-coordinate
   predicates, strict Roos shift/localization theorem, scalar shift interfaces,
   counit word machinery and downstream whole-tower theorem. The latter is a
   consumer and is not imported. No downstream result is assumed.

Sources read: the newest blueprint trace-function definition under
`literature/blueprint/latest/blueprint/sec-fourier-transform/sk-cor-plancherel/`,
plus the node's full extracted nine-step argument, Stacks
`sites-cohomology.tex`, `lemma-derived-limit-is-ok` (0941), and the signed cone
and shift formulas in the existing dependencies. The current blueprint has moved
the trace definition; the DAG's auxiliary normalized comparison still carries the
full extracted argument, used here without altering the blueprint unit.

### Edge cases and validation

- Empty word: both actual functors and b are identity; the retained counit word
  comparison is identity. Empty blocks in parentheses are included.
- Zero complexes and zero maps: all strict maps are degree zero and diagonal;
  the signed coordinate and rho equations still type and include these cases.
- Every integer shift is quantified, including zero, negative and successive
  shifts. `CommShift` retains naturality, zero and addition coherence.
- Identity scheme maps and isomorphisms, arbitrary finite compositions and
  alternative parenthesizations are included by the dependency's constructors.
- Identity coefficient inclusions, repeated fields, and successive extensions
  are permitted without a strictness condition on the algebra maps.
- Empty schemes satisfy the same scheme predicates and are not excluded by any
  nonemptiness or point-existence premise.
- All towers retain their horizontal quotient maps; no quotient complex is
  assumed K-flat over the completed coefficient ring.
- Diagnostic and delivered files were compiled only with the prescribed
  `scompile.py` wrapper. A compile reached the local 60-second limit; the
  wrapper's server confirmation succeeded in 54.2 seconds. Unnecessary
  unfolding of standard derived-category and coefficient-datum witnesses was
  then prevented using the same local irreducibility declarations as the
  completed-compositor normalization dependency. Final compile and delivery
  preflight results are recorded below.

No new DAG nodes, dependency replacements, statement correction, or
STATEMENT-DISPUTED issue is proposed. All auxiliary definitions belong to the
single owning comparison node and are listed in `lean.declarations`.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
