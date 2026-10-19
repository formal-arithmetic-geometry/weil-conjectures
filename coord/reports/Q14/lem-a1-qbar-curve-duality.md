## Worker report

This repairs returned immutable head 04299c54afe3, H3/H5. The module
`Sheaf.DeligneLaumon.QbarCurveDuality` states
`WeilConjectures.QbarCurve.qbarCurveDuality` and its conditional Weil clause
`qbarCurveDuality_weil`. Both theorem proofs are `sorry`; definitions contain
real constructions. All helpers belong to this node and are listed in
`lean.declarations`. No mathematical node field changes.

The returned module transported the Tate action through a freely chosen smooth
orientation. That made orientation equivariance tautological. The repair instead
normalizes the exceptional Frobenius comparison by Mathlib's adjunction mates
correspondence applied to the actual `zlShriekFrobenius` inverse. The resulting
`omegaFrobenius` has no orientation argument. Equivariance of each of the three
ordinary orientations is a separate conclusion in `WeilData`.

Hypothesis and clause correspondence:

- The global datum is `D : FiniteFieldDatum`; `P : D.CoefficientDatum` supplies
  the prime, `P.different`, and the chosen algebraic closure `P.Qbar`.
- `C`, `U`, and `Z` have their displayed scheme-over-k structures. The structure
  map of each has `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`.
  The U/Z properties follow from the geometric hypotheses in the node; they
  express the required coefficient-category domains, with no properness imposed.
- `Smooth (C ↘ Spec (.of D.k))` and `hCdim : Scheme.IsPureDimension C 1`
  state smoothness and pure dimension one, including the empty scheme.
- `j`, `i`, `IsOpenImmersion`, `IsClosedImmersion`, and their `IsOver` instances
  render the named k-immersions. `hj : DenseRange j`, `IsReduced Z`, and
  `hij : Set.range j = (Set.range i)ᶜ` render density and the reduced complement.
- The categories are the recorded `generalAlgebraicallyClosedConstructibleCategory`
  and `GeneralAlgebraicallyClosedCoefficients.Stage`. `Dual` binds the actual
  `CoefQbarVerdier.Duality`, `InternalHom`, and `Dualizing` records. Thus its
  omega is identified with exceptional pullback of the specified coefficient
  unit, and its functor is identified with `homDual`, the restriction of
  `commonStageDerivedInternalHom`. The evaluation and evaluation biduality,
  scalar normalization, exactness and anti-equivalence are inherited from those
  records. There is no free omega or arbitrary dual functor.
- `Data.coefficientSystem : FdCoefficientComparisonSystem` supplies the normalized
  exact coefficient equivalences J_T, including identity on integral objects,
  raw localized Hom groups and the chi-normalized scalar transitions.
  The noetherian, dimension and invertibility witnesses are conclusion data in
  the three `Dual` records, not additional hypotheses on the theorem.
- `Data.orientationC`, `orientationU`, and `orientationZ` give finite smooth
  orientations in dimensions 1, 1 and 0. `smoothIdentification` constructs the
  common-stage maps by the recorded omega comparison, inclusion of the least
  finite stage and its shift comparison. Their endpoints are exactly omega_C
  and omega_U to Lambda(1)[2], and omega_Z to Lambda(0)[0]. The canonical
  zero twist and zero-shift constraints identify the last endpoint with Lambda.
  `OrientationScalar` fixes their scalar squares using the actual dualizing
  scalar map and `orientationTargetScalar`, which uses the recorded Tate-line
  scalar map and shift comparison. Identity extensions are included.
- `Data.localization` is `SfAlgebraicallyClosedLocalization` on these exact
  immersions. Its finite stages are the recorded localizations; its closed
  pullback is the canonical pullback, its direct image is its right adjoint,
  and its exceptional functor is that direct image's right adjoint. Their
  specified units, counits and finite descent are part of the record. The
  zero-functor adjunction from the returned head is therefore unavailable.
- `Comparisons.openIso` and `closedIso` are natural isomorphisms of the whole
  contravariant functors, with targets respectively the actual open pullback
  followed by D_U and the actual localization exceptional functor followed
  by D_Z. They assert both displayed comparison formulas for every object
  with the naturality equations built into natural isomorphisms.
- `finiteOpen`, `finiteClosed`, and `exceptionalScalar` give their finite-stage
  maps. `ComparisonProperties` gives descent to exactly the common comparison
  components, scalar compatibility for both formulas, and compatibility of
  exceptional scalar change with the localization stage comparisons. All
  quantifiers include repeated stages. The inherited Verdier record supplies
  the corresponding evaluation and biduality scalar equations.
- The conditional Weil clause is the second theorem, for the geometric base
  change of a complementary immersion pair over k0. Its hypotheses are the
  same smoothness, dimension, density, reducedness and complement conditions
  on that fibre; finite-type/separated structures on the model and fibre
  immersion instances express the base-change presentation. It concludes
  `∃ B : Data ..., Nonempty (WeilData ... B)` for the same B in all clauses.
- `WeilDualizing` supplies the structure-map exceptional adjoint to the actual
  `zlCommonStageShriek`, its adjunction, and an invertible Frobenius comparison.
  Its `normalized` equation fixes that comparison to
  `mateEquiv adjunction adjunction (TwoSquare.mk ... zlShriekFrobenius.inv)`.
  By Mathlib `mateEquiv_counit` this is precisely compact support of the
  exceptional comparison followed by the counit equals the inverse shriek
  exchange followed by Frobenius pullback of the original counit. Thus this is
  the trace-equivariant exceptional action, with no reference to an orientation.
  `omega_eq` gives the carrier as that right adjoint on the canonical constant
  point object. `omegaFrobenius` evaluates the normalized comparison there,
  follows it by the exceptional image of the canonical constant Weil action,
  and transports only this carrier equality.
- `tateFrobenius` independently constructs the prescribed action on
  Lambda(d)[2d] from `FrobeniusCoefficientTwists.commonDerivedLineMap` and the
  canonical shift comparison. `WeilOrientation` is the non-tautological square
  F*(orientation) followed by this Tate action equals the induced exceptional
  action followed by orientation. `WeilData` asserts this for the very
  `Data.orientationC/U/Z` already chosen, in dimensions 1, 1, and 0.
- `WeilDual` fixes the underlying functor literally to the recorded duality and
  lifts the actual evaluation biduality as a natural isomorphism. `WeilEvaluation`
  imposes the evaluation equivariance square using canonical tensor pullback
  and the induced `omegaFrobenius` just constructed. Its three instances use
  exactly the same exceptional data as the three orientation squares. These
  fix the contragredient structures used in the Weil comparisons.
- `weilPull` uses the normalized Frobenius square `zlFrobeniusSquare` on the
  recorded `sfCommonStageWeilComplex` fixed-pair categories. `WeilData` supplies
  the actual supported exceptional lift; its closed adjunction and its unit
  and counit are fixed to the original ones. Its two natural comparison
  isomorphisms forget to the same B.comparisons maps, as required by
  `openUnderlying` and `closedUnderlying`.
- The `_coefficientsC/U/Z` existential clauses in `WeilData` are `FdFrobeniusComparison` for B's coefficient
  system, so J_T also identifies the two actual Weil-pair categories. No
  stable integral lattice is hypothesized. The only exactness/triangle
  structures used are on the underlying constructible categories; no
  triangulation of fixed pairs is asserted.

Dependency declarations read and reused:

- Mathlib: `AlgebraicGeometry.Smooth`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`, `IsOpenImmersion`, `IsClosedImmersion`, `IsReduced`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `CoefficientDatum`,
  and `geometricFiber`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the raw stages,
  common-stage category, finite inclusions, transitions and shift comparisons.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the canonical derived operations and
  their coefficient comparisons, used through `CoefQbarPullback`, `CoefQbarTensor`
  and `CoefQbarVerdier.homDual`.
- `Sheaf.SixFunctors.CoefQbarVerdier`: `Duality`, `InternalHom`, `Dualizing`,
  `pullbackInclusion`, `inclusionTransition` and the finite duality data.
  `Dualizing` uses the recorded constructible exceptional coefficient system
  from `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`.
- `Sheaf.Paper.SfLocalizationAllStages`: `SfAlgebraicallyClosedLocalization`,
  `SfSupportedLocalization`, `SfWeilLocalization`, `sfLocalizationFiberMap`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the integral,
  rational and common-stage twisting coefficients. The canonical finite
  scalar map is `RationalSmoothPurityCanonical.lineScalar` from
  `Sheaf.Paper.PuritySourceTransports`; its underlying map is fixed by root
  scalar transport and completion, not an arbitrary line isomorphism.
- `Sheaf.Paper.RationalCoefficientCategoryComparison` and its public definition
  dependencies: `FdCoefficientComparisonSystem` and `FdFrobeniusComparison`.
- `Sheaf.Paper.SfWeilSheafComplex`: the common-stage fixed pairs and forgetful
  functor. `Sheaf.Paper.WeilIndSheafCategory`: `zlFrobeniusSquare`.
  `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical`: `commonDerivedLineMap`.
  `Sheaf.Paper.FieldWeilShriekShiftData`: canonical common-stage tensor pullback.

Edge cases checked: C empty (pure dimension is vacuous); empty Z (dimension-zero
orientation, no nonempty maximum); U=C; U empty only when C is empty by density;
zero complexes; E=F and identity scalar maps; several components permuted by
Frobenius; and Weil complexes without a Frobenius-stable integral lattice. For
C=A1 and Z={0}, the closed comparison has direction i*D_C Lambda to D_Z Ri!Lambda,
both Lambda(1)[2]; this checks the contravariance and the signs of shift/twist.

Searches retained in `searches.jsonl` and the node's `mathlib_searches`:
`msearch.py leanfinder` queried rational Verdier duality on a smooth curve with
natural open/closed comparisons and Weil pairs (only unrelated stalk lemmas).
`msearch.py loogle` queried the expected project names (unknown identifiers:
this is not evidence of absence); its quoted Verdier search found only generic
Verdier localization. `msearch.py grep` queried Verdier/dualizing and expected
names in Mathlib (generic derived functors and no curve-duality theorem).
`rg` of the upstream `WeilConjectures` source and the shared `lean/Sheaf`
found the recorded coefficient, localization and duality interfaces reused here,
but no theorem with this entire curve statement. The upstream etale dualizing
complex alone is on another coefficient category and is not substituted for the
recorded rational coefficient-passage construction.

No STATEMENT-DISPUTED flag, statement correction, new node or dependency-record
repair is needed. The source is the current blueprint curve-heart proof,
Steps 2–3, together with the node's seven explicit proof steps.

## Second reading by Q14

This is a self-check; the dispatcher forbids starting another agent, and the
maintainer performs the independent review. Reopened the current node, full
retained module and blueprint Steps 2–3, along with `CoefQbarVerdier.InternalHom`,
`Dualizing`, `Exceptional`, `zlCommonStageShriek`, `zlShriekFrobenius`, constant
Weil coefficients, and Mathlib's `mateEquiv` and `mateEquiv_counit`.

H3/H5: the returned orientation-conjugated action has been removed. The new
`WeilDualizing.normalized` binds the exceptional comparison to the mate of the
canonical shriek exchange. `omegaFrobenius` depends on these exceptional data and
the canonical constant point Weil object, and never on `SmoothOrientation`.
The `WeilOrientation` squares for C, U, Z assert equivariance against the prescribed
Tate action. The evaluation squares use those same induced actions; the two
Weil comparison isomorphisms use those evaluation-normalized dual lifts and
forget to B's ordinary comparison components. Smooth-purity Weil equivariance
is therefore needed to establish the orientation clauses.

Matched each hypothesis and each clause against the correspondence above.
The actual internal Hom, exceptional coefficient unit, supported-localization
closed adjoint, finite representatives and scalar squares, normalized coefficient
system J_T, and induced fixed-pair comparisons are retained. The only postponed
proofs are the two named theorems with their complete proof docstrings.

Rechecked empty C and Z, U=C, K=0, identity coefficient extensions, and
A1 minus a point. For two components permuted by Frobenius and Z empty, the
exceptional action is induced before any orientation is supplied: changing an
orientation changes the asserted equivariance equation, not the action. This
is the counterexample that exposed the returned definition's tautology.

## Compile and delivery checks

The initial required dry run of the retained packet timed out both locally and
on server confirmation. A bounded diagnostic pinpointed the componentwise
counit field (whnf at line 356). Replaced its identical content by the existing
Mathlib mates normalization to avoid that elaboration cost; no clause is dropped.
The server wrapper's 60-second limit is unchanged.

Resumed validation on 2026-10-19: the retained packet passed `deliver2.py Q14
lem-a1-qbar-curve-duality --no-push`, including the sandbox compile, library
compile and server preflight (dry-run commit d25ba55d91). No compile warning or
error was reported. The current read clone has no module for this item and its
node differs from this packet only in `lean`. Rechecked the returned H3/H5
against `ExceptionalFrobeniusNormalized`, `WeilDualizing`, `omegaFrobenius`,
`WeilOrientation` and `WeilData`: the inverse shriek exchange has exactly the
source required by `mateEquiv`; the mate's counit equation fixes its trace
normalization; evaluation at the canonical constant point pair induces the
dualizing action before any orientation is supplied. All three orientations
and all three evaluation equations use these same induced actions. The
component-swapping example therefore changes the orientation equivariance
condition rather than defining a new action. The ordinary statement, finite
scalar squares and underlying comparison components are retained.
