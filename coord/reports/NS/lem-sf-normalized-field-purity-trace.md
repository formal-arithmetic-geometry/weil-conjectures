## Worker report

The primary module states normalized field purity, inverse purity and the actual exceptional
counit trace, for rationalization, finite coefficient extension and each common-stage
inclusion. All theorem proofs are postponed. All helper definitions are actual aliases
or compositions of recorded constructions. `Conclusion` packages the assertions; it
is not used to select data from an unproved existence statement.

Hypothesis and clause correspondence:

- `P : PurityFiniteSetting.{u}` contains the finite-field datum, prime ell distinct
  from p, fixed coefficient closure, finite subextension E and positive quotient level.
  Its quotient rings, valuation ring and uniformizer are the recorded ones.
- `X.Over`, `Y.Over`, `LocallyOfFiniteType`, `QuasiCompact` and absolute `IsSeparated`
  give precisely separated finite-type schemes over the fixed algebraic closure.
  `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`, `r : ℕ`
  and `SmoothOfRelativeDimension r f` give the stated smooth separated map and pure
  nonnegative relative dimension. No properness, nonemptiness or positive dimension
  is assumed.
- `S : ConstructibleExceptionalCoefficients.System ...` is the recorded actual
  compact-support/exceptional operation system, with its etale-origin adjunctions,
  left realizations and normalized coefficient comparisons. This is construction
  data for the operations, not a hypothesis of purity or of its trace equations.
- `A : AdicPurityScalarNaturality.Data ...` is the simultaneous normalized integral
  natural family that the node says to choose once. Its categories are the actual
  completed-coefficient derived-complete uniform finite-Tor subcategories. Its
  `finiteReductions` fixes the prescribed finite smooth-purity maps, and its
  coefficient comparisons use ordinary derived tensor and the specified associators.
- `rationalGamma` is exactly the recorded canonical `rationalIso`, at `stageSetting
  P E`. Its source is `rationalSource` (derived pullback, Tate line, even shift),
  and its target is the same system's exceptional functor. `closedGamma` is exactly
  `commonIso` in the common finite-stage category. Their inverses are `Iso.inv`.
  `smallGamma` is the published `smallModelIso` through the fixed algebra equivalence;
  it retains the model transport needed for each actual stage inclusion.
- `trace` is literally `P.map gamma.hom ≫ adj.counit.app K` for that same component
  and adjunction. It defines all integral, rational and common-stage traces uniformly.
- `Conclusion.localization` and `localization_normalized` use the recorded canonical
  source localization, including tensor/line/shift constraints. `rationalizes` gives
  all three displayed equations for integral-to-field passage, with the actual
  `gLocalization` and `S.fields.rationalizationComparison.q`.
- `Conclusion.a` is a natural source comparison; `a_canonical` identifies every
  component with the existing `sourceScalar`, rather than an unspecified isomorphism.
  `extension` gives the three equations for every finite E ≤ F using the actual
  rational exceptional comparison `b` and support comparison `c`.
- `PassageEquations.purity` is C_X(gamma) followed by b = a followed by gamma'.
  `PassageEquations.inverse` is C_X(eta) followed by a = b followed by eta'.
  `PassageEquations.trace` is C_Y(t) = c at H(K), then P'(a), then t' at C_Y(K).
  These are the node's right-to-left formulas written in Lean composition order.
- `rational_natural` and `closed_natural` cover all morphisms in the respective
  actual categories. The use of isomorphisms gives both inverse identities and
  well-defined inverse maps without any independent choice of orientation.
- `source_unit`, `source_composite`, `exceptional_unit`, `exceptional_composite`,
  `support_unit`, `support_composite` retain the actual tensor unitors and
  three-field associators on both X and Y. These are equations of natural
  comparisons, so their substitutions in the three passage equations express
  compatibility with identity and composite coefficient passages.
- `descends` gives all three equations for every common-stage inclusion, with
  canonical `commonSourceComparison`, `S.common.commonComparison.b` and `.q`.
  The source comparison is the inverse canonical source presentation on the
  literal pair. `common_source_composite` is its compatibility with enlargement
  E ≤ F, using exactly the published scalar and inclusion-transition comparisons.
  The corresponding b and c enlargement equations are retained by `S.common`.
- `common_check` says that any finite family of arrow equalities is checked on
  representatives in one common finite field, after enlargement if necessary.
  It does not assume that a transition functor is faithful. In particular, the
  finite family may be the equations for gamma, eta and t in the node.
- No functor reducing a field to a finite quotient is introduced. Positive-level
  finite reductions occur only in the supplied integral family and its normalization.

Dependencies used:

- `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum`, the actual
  six-functor setting, reexporting the recorded coefficient-stage operations.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the intrinsic signed integral,
  rational and common-stage Tate lines used by the canonical purity source.
- `Sheaf.Paper.SmoothPurityMap`: `PurityFiniteSetting.smoothPurityMap`.
- `Sheaf.Paper.SmoothTrace`: `PurityFiniteSetting.smoothTrace` and
  `coefficientValuedSmoothTrace`; they are the finite reductions specified by A.
- `Sheaf.Paper.AdicPurityScalarNaturalityData` (node
  `def-pur-adic-purity-scalar-naturality-data`): `Data`, `source`, `target`,
  `operation`, `fieldStage`, the actual simultaneous integral family.
  `Sheaf.Paper.AdicPurityScalarNaturality` is a private proof import.
- `Sheaf.Paper.RationalSmoothPurityCanonical` (node
  `def-pur-canonical-rational-purity-realization`): `rationalIso`, `smallModelIso`,
  `commonIso`, `stageSetting`, `rationalSource`, `commonSource`, `sourceScalar`,
  `commonSourceComparison` and their full actual-operation presentations.
- `Sheaf.Paper.RationalScalarComparisonData` (node
  `def-pur-rational-scalar-comparison-data`): `RCat`, `Q`, `H`, `G`, `O`, `T`,
  `b`, `c`, `gLocalization`, `SourceLocalizationNormalization`, `unit`, `alpha`,
  `UnitEquation` and `CompositionEquation`. This definition node owns the
  coordinate declarations used in the signature and is cited in stmt_deps.
  The theorem node `lem-pur-rational-scalar-comparison-identification` remains
  in proof_deps, with its module imported privately in the primary module.
  Its theorem and `Result` are not used by the statement. The natural-language
  statement and proof are unchanged.
- The remaining proof dependencies are imported privately as the stage-3 plan:
  RationalLatticeAdicDomain, PbcRationalTransport, QcqsCompactSupportRealization,
  SixFunctors.RationalOperations, PbcDescentFunctors,
  CommonStageSmoothOperationIdentification, GeneralAlgebraicallyClosedCoefficients,
  IntegralCompactSupportCoefficientComparison.

Edge cases read before writing: r=0; empty X or Y; zero complexes and torsion
lattices whose rationalizations vanish; E=F and E=F=L; the positive level n=1;
ramified extensions (ordinary tensor and the recorded scalar model are retained);
unequal coefficient-stage representatives; enlargements after equality; an empty
finite family of equalities (m=0, the least coefficient field supplies a stage).
No edge case requires an additional assumption.

Searches for an exact existing statement:

- msearch LeanFinder: "A normalized smooth purity isomorphism and its inverse and
  exceptional counit trace commute with rationalization and finite coefficient
  field extension". Eight normalization-of-schemes results, no match.
- msearch Loogle: `"counit", "map"`. Twelve generic comma-category counit results,
  no statement identifying this smooth purity family and trace.
- msearch grep: `purity|smoothTrace|smoothPurity` in Mathlib/CategoryTheory: zero hits.
- msearch LeanSearch: "Smooth purity and its inverse and counit trace commute with
  localization of integral coefficients and extension of coefficient fields".
  Eight ring-theoretic localization/smoothness/trace results, no match.
- rg in lean/WeilConjectures for this node id and normalized field purity names:
  no declaration for the item. The WeilDual comment mentions a different equivariance
  node. rg in lean/Sheaf found the canonical rational isomorphisms and the sibling
  NormalizedIntegralPurityTrace; neither states the field inverse and trace equations
  for all three coefficient passages and their common-stage coherence.

No new independent notion or definition node was needed. No statement correction.

The local residue-field invertibility instances are constructed from
`PurityFiniteSetting.coefficientPrime_isUnit_stalk` and the residue homomorphism;
they are consequences of ell != p, not additional hypotheses. The real helper
`commonSourceScalar` includes the published scalar comparison after the existing
`commonCategory_eq` category transport. `CommonSourceComposition` names its
explicit enlargement square, still required as `Conclusion.common_source_composite`.
These are owning-node helpers and introduce no independent mathematical notion.

## Repair of returned delivery

The returned immutable head was `6a03155fbf40`. H2 is repaired by replacing the
added theorem stmt_dep with its owning definition node,
`def-pur-rational-scalar-comparison-data`, and publicly importing
`Sheaf.Paper.RationalScalarComparisonData`. The theorem remains in proof_deps
and is imported privately. The two advisory definition nodes for the integral
family and canonical rational realization are also cited explicitly.

The three consumer files from the returned packet are removed from the delivery:
`AffineSpaceZeroSectionPurity`, `AffineSpaceZeroSectionPurityData`, and
`WfTensorUnitSquareData`. Validation below uses the live published library.
No consumer rewrite or unowned module is included.

The owning node retains three modules to bound per-file compiler work:

- `NormalizedFieldPurityTraceData`: real components, local residue instances,
  literal traces, and the three passage equations.
- `NormalizedFieldPurityTraceCommonStage`: the included scalar comparison and
  the exact common-stage source-enlargement square.
- `NormalizedFieldPurityTrace`: the full conclusion and the one postponed theorem;
  it imports the two helper modules and all recorded proof dependencies.

All three belong to this same node; the helper modules contain no postponed proof.

## Validation

All three owning modules compile against the live published library, without
consumer overrides. The library checks took 14.4 s (Data), 30.6 s (CommonStage),
and 42.0 s (primary), all within the 60-second limit, with no unaccepted warning.
The earlier consumer failures did not reproduce. The primary theorem remains
`sorry`, as required for stage 2. The two helper modules contain no postponed
proof or axiom. The required dry run passed: `OK (dry run): commit
cbebfd3da07 passes the preflight and compiles; nothing pushed`. Its staged
packet contains only the item node, report, and the three owning modules.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
