## What changed

Proved the completed and finite signed comparison existence/uniqueness theorems using
internal Hom over the ringed site equivalence. The maps are conjugation by the fixed
positive comparisons. Adjunction and evaluation on unit sections prove uniqueness.
Existing public signatures, definitions and public imports are retained.

## Proved and sorry left

Original holes closed (2 of 6):

- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_signedLineMaps`.
- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_finiteSignedLineMaps`.

Original holes remaining (4), all with node `def-weil-frobenius-coefficient-twists`:

- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_positiveLineMaps`.
- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_finitePositiveLineMaps`.
- `WeilConjectures.FrobeniusCoefficientTwists.existsUnique_pullbackAugmentation`.
- `WeilConjectures.FrobeniusCoefficientTwists.pullbackAugmentation_isIso`.

Holes added: zero. No split statements. The full module compiled in 48.8 seconds.
Further work is retained in scratchpad and is not part of this packet.

## No longer needed

None. Both original proof dependencies for localization remain used. The new signed
proof uses `PurInverseImageHomComparison` and the ringed inverse-image unit comparison
from `CartesianCoefficientTwists`. No parent or unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous DAG proof documented only the already completed localization descent.
The signed comparison arguments are now explicit in Lean. No statement repair or
consumer adaptation was needed.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
