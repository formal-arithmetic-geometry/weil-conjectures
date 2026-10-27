## What changed

In `Sheaf.Paper.CommonStageWeilShriek`, proved the proper pullback adjunction by
`sfModelPull_isLeftAdjoint`. Proved that the actual common-stage Frobenius pullback is
an equivalence using its inverse scheme automorphism, normalized composition, and the
common-stage identity comparison. Applied the existing forward and inverse mate
isomorphism theorems to prove both specified Frobenius exchanges invertible.

The Frobenius equivalence proof follows the already-proved private helper in
`SfCommonStageDirectImage`; it is local here because that helper is private. All public
signatures, adjoint choices, mate formulas and compact-support definitions are unchanged.
Added private proof imports for `SfCommonStageDirectImage`, `CommonStagePullbackIdentity`,
`InverseMateEquivalence` and `Morphisms.FiniteType`. Updated the existing node's proof
and dependencies to record this route. No new module or statement was introduced.

## Proved and sorry left

Closed 3 of the item's 5 original holes, with no holes added:

- `WeilConjectures.zlPull_proper_isLeftAdjoint`.
- `WeilConjectures.zlProperFrobeniusMap_isIso`.
- `WeilConjectures.zlOpenFrobeniusInverseMap_isIso`.

Two original holes remain, with their signatures and source/proof docstrings unchanged,
both attached to `def-zl-common-stage-weil-shriek`:

- `WeilConjectures.zlPull_open_isRightAdjoint`.
- `WeilConjectures.zlCommonStageShriek_recorded`.

The private helper `zlShriekFrobenius_isEquivalence` is fully proved. The three closed
holes use the existing recorded lower theorems; this report does not claim that their
entire transitive axiom closure is already free of unfinished proofs. This is a partial
proof delivery, not a decomposition: zero split-off statements and zero added holes.
The module compiled through `lcompile.py` without diagnostics before import cleanup;
the delivery tool repeats compilation and runs the declaration/axiom probes.

## No longer needed

Removed the unused private import `Sheaf.Paper.QcqsCompactSupportRealization` from the
item. This does not assert that the module is globally unused: it is still part of
other proofs and is relevant to the unfinished recorded-action comparison.
The explicit `RationalCoefficientCategoryComparison` import tested during development
was redundant through `CommonStagePullbackIdentity` and is omitted.

The direct hand-written forward/inverse mate-pasting calculations are unnecessary:
the existing categorical mate theorems supply exactly those results. No DAG node or
library module is withdrawn, and no unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item's definition node had an empty proof and proof dependency list despite five
proof holes. Its retained docstrings do state the intended argument; the node now records
the completed portions and explicitly identifies the two unfinished portions.

The proper-adjoint existence clause was already a special case of the existing
`sfModelPull_isLeftAdjoint`, even without a properness hypothesis. The original signature
retains properness. The existing `sfQbarLocalizationCommonStage` and
`sfRationalLocalizationTriangleOrthogonality` theorems require separated structure
morphisms, whereas this item does not. They cannot directly discharge its open-adjoint
hole without an additional argument. No separatedness assumption was added.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
