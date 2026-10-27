## What changed

Replaced the item theorem's sorry with a complete proof from the bounded-below
proper factor and proved categorical facts. The original theorem signature and
public imports are unchanged. The original input is bounded by
`sfIntegralStandardTruncations`; exact open extension preserves a lower bound.
The compact-support factorization then combines the proper component with the
proper direct image of the open component.

The private `open_scalar_mate_isIso` is proved for arbitrary coefficient changes
and all ambient inputs. It localizes the proved ordinary open restriction mate,
then applies Mathlib's iterated-mate/conjugation identity. It does not apply the
existing holed `PurCompactSupport.openComparison_isIso`. The latter remains in
its original module without modification.

One genuine analytic factor remains in the new module: proper scalar comparison
on a bounded-below input. It has no open immersion or compactification and no
constructibility, completeness, finite Tor or finite-field scheme hypotheses.
Its docstring and node specify the normalized integral-to-rational-to-native
coefficient factorization, the two existing bounded proper comparisons and the
pasted-counit identification of the actual map. This is the proper factor of the
original plan, not the compact-support assertion under another name.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.LocallyFiniteAdicCompactSupport.native_compact_support_scalar_mate_invertible`.
Its body is complete. The private open-scalar-mate helper is also complete.

Added one hole:
`WeilConjectures.LocallyFiniteAdicCompactSupport.native_proper_scalar_mate_bounded_below`,
in `Sheaf.Paper.NativeProperScalarMateBoundedBelow`, with node
`lem-sf-native-proper-scalar-mate-bounded-below`.

Counts: one original hole closed, one strictly narrower proper-factor hole added;
zero holes remain in the item module and one remains in the delivery. This is a
decomposition, not a net sorry-free proof. No definition contains a hole.

Validation: the new proper-factor module compiled in 10.5 seconds and the item
compiled in 8.1 seconds through lcompile.py, with no warnings.

## No longer needed

No original import was removed: the item originally had only its public data
import, which its statement still needs. Three proof-only imports support the
new route. No existing module or declaration is withdrawn.

The item no longer needs these original planned dependencies, even in the new
proper-factor plan:

- `lem-coef-integral-residue-tor` (`Sheaf.Paper.IntegralResidueTor`).
- `lem-kun-dimension-finite-type` (`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`).
- `lem-pc-kflat-resolution` (`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`).
- `lem-per-continuous-rational-derived-realization` (`Sheaf.Paper.ContinuousRationalDerivedRealization`).
- `lem-pur-derived-change-of-rings` (`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`).
- `lem-sf-integral-compactification-system-realization` (`Sheaf.SixFunctors.IntegralCompactificationSystemRealization`).
- `lem-sf-integral-direct-image-constructible` (`Sheaf.Paper.SfIntegralDirectImageConstructible`).
- `lem-sf-integral-open-reduction-comparison` (`Sheaf.SixFunctors.IntegralOpenReductionComparison`).
- `lem-sf-open-finite-constructibility-interval` (`Sheaf.Paper.OpenFiniteConstructibilityInterval`).
- `lem-sf-ringed-open-total-tensor-kflat` (`Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat`).
- `lem-weil-pbc-finite-type-over-noetherian`.
- `lem-weil-pbc-integral-stratified-perfect-characterization` (`Sheaf.Paper.IntegralStratifiedPerfectCharacterization`).
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`.
- `prop-weil-pbc-direct-image-limits` (`Sheaf.Paper.CompletedDirectImageLimits`).

The lower bound comes directly from the input's intrinsic standard-truncation
API and exactness of open extension. This removes the proposed detour through
constructibility and Tor bounds of the open object, compactification systems,
completed direct-image limits and direct-image finiteness. The formal open mate
uses exact localization and conjugation, so it requires no new K-flat open-tensor
argument. The analytic coefficient-realization, localization, bounded algebraic
closure pushforward, flatness and pasted-mate normalization dependencies remain
in the new proper-factor node; they are not claimed pruned globally. Other
parents can still require any listed module.

## Where the brief, the DAG or earlier work was wrong

No statement was changed or disputed. The original proof plan asked for more
properties of the open extension than its proper factor requires: the latter
needs only a lower bound. The existing openComparison_isIso declaration is still
sorry, so treating its availability as a completed proof would conceal another
hole; the delivered private helper proves that step directly instead.

The current server queue listed this item as `proof route`, with no rework or
build-error entry. The source and target statements are preserved.

## New nodes

`lem-sf-native-proper-scalar-mate-bounded-below` realizes the analytic proper
factor in `Sheaf.Paper.NativeProperScalarMateBoundedBelow`, with node
`lem-sf-native-proper-scalar-mate-bounded-below`. It retains the item's
chapter and unit and records the full argument and Mathlib searches. Blueprint
and DAG searches found no existing node for this precise native proper mate.
The ancestor command returned None for this item chain; the node records that
result and the inherited cor-coef-verdier-weil-equivariance anchor in its place.
Identity maps, empty schemes, zero inputs and nonconstructible bounded-below
inputs were checked against the proposed argument. No change record is needed:
only the item, its own node and the new module/node are changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeCompactSupportScalarMateInvertible": "ab58f1701c4fb3b02c1aceef1ce25df67ed058ee", "Sheaf.Paper.NativeProperScalarMateBoundedBelow": "7c27cac33b4085326c30dc290a33678983a8799f"}, "results": {"Sheaf.Paper.NativeCompactSupportIntegralLocalization": {"hash": "a40431ed8ef152b8f3fc7ba4e819a776c2b222a4", "status": "OK"}}, "seconds": 59, "time": "2026-10-28T04:15:16+0800", "transitive": 0, "version": 1}
```

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
