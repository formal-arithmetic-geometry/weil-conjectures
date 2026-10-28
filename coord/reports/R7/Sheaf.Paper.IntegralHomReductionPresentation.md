## What changed

The item theorem `WeilConjectures.IntegralHom.reduction_presentation_exists_at` is now proved by
combining two strictly smaller statements. `Sheaf.Paper.IntegralHomReductionComponents` supplies
a finite-level target `TensorPresentation`, and
`Sheaf.Paper.IntegralHomReductionNormalization` supplies a `ReductionPresentation` with that
fixed target. The item module imports these two proof modules and constructs the required
`Nonempty` witness.

## Proved and sorry left

The item theorem `reduction_presentation_exists_at` is proved, with zero `sorry`s left in the
item module. Two strictly smaller split statements remain as named sorries:
`WeilConjectures.IntegralHom.reduction_target_exists` (node
`lem-sf-integral-hom-reduction-target`) and
`WeilConjectures.IntegralHom.reduction_normalization_exists` (node
`lem-sf-integral-hom-reduction-normalization`). No definitions contain `sorry`.

## No longer needed

The original proof-only imports `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`,
`Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`, and
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` are no longer imported by the
combining module. Their declarations remain recorded as dependencies of the normalization
split node, where they are needed for the eventual proof.

## Where the brief, the DAG or earlier work was wrong

The original proof step bundles construction of the finite-level tensor target, the comparison,
and the full sectionwise normalization into one existential. Given the available declarations,
that bundled obligation cannot be discharged directly. The delivery records the two actual
interfaces needed by the constructor: existence of the target and existence of a normalized
reduction presentation over a fixed target. The target theorem is unchanged.

## New nodes

`lem-sf-integral-hom-reduction-target` is implemented by
`lean/Sheaf/Paper/IntegralHomReductionComponents.lean`.

`lem-sf-integral-hom-reduction-normalization` is implemented by
`lean/Sheaf/Paper/IntegralHomReductionNormalization.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomReductionComponents": "51631fde4f1185a9abaa6d520746c0977ea4675f", "Sheaf.Paper.IntegralHomReductionNormalization": "358b58294b08bca6487cd63f58a1ff4195a9e188", "Sheaf.Paper.IntegralHomReductionPresentation": "0e5216560a3b2842e8613af3378b2363613c69c3"}, "results": {"Sheaf.Paper.IntegralHomModelsExist": {"hash": "0b8abf2fceaad79febc3ab025a333a597e4ccdd3", "status": "OK"}}, "seconds": 130, "time": "2026-10-28T08:11:11+0800", "transitive": 0, "version": 1}
```

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
