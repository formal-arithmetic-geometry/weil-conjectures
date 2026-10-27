# WeilConjectures.GeneratorReduction.integralConstantCompleteTransport

## Reason

The bridge uses the actual functor H on the published integral constructible objects.
The general constant-completion equivalence is stated on local ideal-complete
subcategories. A coefficient-only transport lemma isolates the identification of that
locus and its Hom bijection with the existing IsSfDerivedComplete and H definitions.
It is independent of all compactification and word comparisons.

## Old

No declaration named
`WeilConjectures.GeneratorReduction.integralConstantCompleteTransport` existed.
The item had separate sorry proofs of `completedComparison_existsUnique` and
`comparisons_isIso`.

## New

A new proof dependency in `Sheaf.SixFunctors.IntegralConstantCompleteTransport`
states that H carries every sfIntegralConstructible object to a complete constant
coefficient object, and that H.map is bijective between the ambient Hom sets of
any two such objects. Its exact signature is in the accompanying new node.
The item proves its two auxiliary theorems from that coefficient-only statement,
open reconstruction effectivity, and the normalized word reconstruction theorem.
All existing public declarations, signatures, definitions and public imports are unchanged.
No target statement or definition used by a target changes meaning.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.IntegralConstantCompleteTransport | new S8 module | New theorem only. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | S8 | Private proof import; two auxiliary proofs completed. |

The new module has no pre-existing users. The item imports it privately, so its own
consumers retain the same public interface. No consumer adaptation is needed.

## Status

landed 20261025T203151-L-2788743 2026-10-25 (merge of deliver/S8/Sheaf.SixFunctors.IntegralCompactificationComparisonBridge)
