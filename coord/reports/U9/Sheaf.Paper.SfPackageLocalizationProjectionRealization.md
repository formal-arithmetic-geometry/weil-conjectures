## What changed

Proved `sfPackageLocalizationRationalization` in
`Sheaf.Paper.SfPackageLocalizationProjectionRealization`, preserving its statement and
all definitions. The supplied integral boundary is descended through scalar
localization, using the existing localization theorem in the proof-only import
`Sheaf.Paper.ScalarExtensionExactIntrinsic` and Mathlib's full faithful precomposition.
Private proved coefficient-comparison lemmas derive the first two triangle squares
from the specified composition, open/proper identification and unit/counit equations.
The third square follows from the descended boundary. Reflection through the
constructible inclusion and exact rationalization prove distinguishedness.

Updated proof step 5 and proof provenance of the existing node to record this argument.
Local reducibility settings avoid unfolding the rational triangulation choice, integral
constructibility predicate and tensor-Hom composition. The finite-image proof uses
local transparency settings to avoid expensive composite-map instance inference.
All public declaration signatures and definition bodies are preserved.

## Proved and sorry left

Closed one of the five existing holes:
`WeilConjectures.sfPackageLocalizationRationalization`.
No holes added or split off.

Four existing holes remain, all attached to
`lem-sf-package-localization-projection-realization`:

- `WeilConjectures.sfPackageLocalizationIntegralTower`
- `WeilConjectures.sfPackageLocalizationCommonStages`
- `WeilConjectures.sfPackageLocalizationWeil_rational`
- `WeilConjectures.sfPackageLocalizationWeil_common`

## No longer needed

None. Existing imports and dependencies are retained for the unchanged finite-image,
integral-tower, common-stage, Weil and projection arguments. The rationalization proof
uses the existing scalar-localization interface rather than introducing intermediate
unproved statements.

## Where the brief, the DAG or earlier work was wrong

No statement or blueprint correction. This is a partial delivery: the rationalization
refinement is proved, while the other four named obligations retain their original
proof plans.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
