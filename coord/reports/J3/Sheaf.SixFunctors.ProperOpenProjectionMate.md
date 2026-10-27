## What changed

The finite-coefficient proof uses the canonical Cartesian open base-change tensor
square, the localized clopen counit, and the categorical tensor-square mate transfer.
Private proved helpers identify the supplied open compositor and the two projection
maps with their published normalizations. The new module
`Sheaf.SixFunctors.ProperOpenPullTensorComposition` proves compatibility of pullback
compositors with tensor, which the open-compositor calculation needs.

The strict-system proof works before evaluation. It uses the supplied
`Realizations.ringedTensorCoherence`, the open-adjunction Hom bijection, and the
normalizations of gamma and the open tensor comparison. The new module
`Sheaf.SixFunctors.SystemProperOpenLambdaExchange` identifies the prescribed lambda
with proper exchange followed by the inverse open unit, by factoring through the
canonical clopen lift and pasting adjunction mates.

All existing public signatures and public imports are preserved. The component
construction of `properOpenTensorIso` now takes the inverse component directly from
the published natural isomorphism, avoiding the expensive `asIso` inverse recovery.
Its forward map is identical. The four other direct consumers compiled unchanged:
`ForwardProductCoordinateTransport`, `CompositionProjectionData`,
`CompositionProjectionMate`, and `TriangleProjectionNormalForm`.
See `coord/changes/proper-open-tensor-component.md`. No adopted source module changes.

## Proved and sorry left

Closed both original holes, without changing their statements:

- `AlgebraicGeometry.ProEtale.properOpenProjectionMate`;
- `WeilConjectures.IntegralSystemRealization.properOpenProjectionMateSystems`.

Both realize `lem-sf-proper-open-projection-mate`. The two new theorems are also
proved: `AlgebraicGeometry.ProEtale.properOpenPullTensorComposition` and
`WeilConjectures.IntegralSystemRealization.systemProperOpenLambdaExchange`.
The latter uses the exact shared predicate `CategoryTheory.OpenExchangeUnitFormula`;
its proof combines abstract adjunction pasting with the geometric compositor equations.

Original holes closed: 2 of 2. Holes added: 0. Holes remaining in this delivery: 0.
There is no unfinished split, no admitted private helper and no hollow definition.
The existing dependency statements retain their independent proof obligations.

Validation: the item compiled in 40.8 seconds before removal of temporary profiling
options. The new pull/tensor theorem compiled in 10.7 seconds and the complete
lambda normalization in 10.6 seconds. The four unchanged direct consumers of the
repaired definition compiled against it. The final combined sandbox compilation
passed for all three modules (result `53603fa7e729eae3f99b150c`); its sole unused-simp
warning was removed from the final file. Both original theorem signatures were
checked verbatim against the shared source.

## No longer needed

Removed direct proof imports:

- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`;
- `Sheaf.Paper.CoefficientSystemDerivedComparison`;
- `Sheaf.Paper.RingedExchangeTensorCoherence`;
- `Sheaf.Paper.ProjectionMateExact`;
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.

The proof does not use `lem-sf-clopen-comparison-tensor-square`
(`Sheaf.SixFunctors.ClopenComparisonTensorSquare`): the already proved canonical
fixed-coefficient tensor square and the localized clopen counit give the finite
alpha calculation directly. It does not use
`lem-sf-semilinear-proper-open-mate-pasting`
(`Sheaf.SixFunctors.SemilinearProperOpenMatePasting`): the intrinsic gamma adjunct
field and the explicit lambda/exchange calculation suffice for systems.

Removed unused top-level tool approvals:
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-pbc-ringed-exchange-tensor-coherence`,
`lem-weil-pbc-ringed-projection-mate-exact`,
`lem-pur-coefficient-system-derived-comparison`,
`lem-weil-pbc-mate-pasting`, and
`lem-sf-semilinear-proper-open-mate-pasting`.
The strict-tower, open-tensor and integral-realization approvals remain in order.
The tensor-square mate-transfer node remains used. These are removals from this
proof route; no module is withdrawn, and transitive or independent users still count.
The unit `sk-rem-sf-pf-done` has no realized proof steps to bypass.

## Where the brief, the DAG or earlier work was wrong

The planned ringed-module tensor-square statements are presented in categories
different from the fixed ModuleCat-valued sheaf categories used by the finite
assertion. A presentation bridge is unnecessary: the library already proves the
canonical fixed-coefficient Cartesian tensor square and localized clopen counit.
For systems the supplied realization record already states the ringed tensor
coherence equation in the required category. The remaining normalization is a
separate adjunction calculation, not a deduction from evaluated equalities.
No statement is disputed or weakened. No arbitrary data is chosen from existence.

## New nodes

`lem-sf-proper-open-pull-tensor-composition`, realized by
`Sheaf.SixFunctors.ProperOpenPullTensorComposition`, proves tensor compatibility of
the canonical exact pullback compositor. Its proof uses uniqueness of mates,
the published inverse-image tensor comparisons, and the compositor adjunctions.

`lem-sf-system-proper-open-lambda-exchange`, realized by
`Sheaf.SixFunctors.SystemProperOpenLambdaExchange`, gives the independent intrinsic
lambda/exchange normalization. Its proof factors the pullback square through the
canonical clopen lift, uses compositor associativity and beta's transpose, and
pastes the open and proper units. The public predicate
`CategoryTheory.OpenExchangeUnitFormula` writes this exact component formula once
for arbitrary categories and functors; sharing that interface avoids repeated
derived-category reductions when applying it. The private square-factor and open-unit
formulas use the same approach. This lemma has no tensor object or realization parameter and is strictly one normalization step of the system argument.

Change record: `coord/changes/proper-open-tensor-component.md`.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
