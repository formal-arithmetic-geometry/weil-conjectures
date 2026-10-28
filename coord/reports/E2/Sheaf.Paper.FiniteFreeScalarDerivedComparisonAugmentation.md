## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralFiniteScalar.finiteFreeScalarDerivedComparison_augmentation`
in `Sheaf.Paper.FiniteFreeScalarDerivedComparisonAugmentation`, preserving its complete
signature and existing public import. Added the private proof import
`Sheaf.Paper.ProfinitePointPullback`.

The exact degree-zero single functor sends `hS` to a short exact sequence of complexes.
Mathlib's canonical cone augmentation theorem proves that
`CochainComplex.monoCokernelAugmentation S` is a quasi-isomorphism. The finite-limit and
finite-colimit clauses of `profinite_point_pullback`, composed with geometric inverse image
and lifted through `mapMod`, make `pointPull Λ Z` exact. Mathlib's homology-preservation
instance then proves the requested degreewise pullback is a quasi-isomorphism.

Updated the item's node to this proof route. Suppressed the unused-variable linter only
for the existing theorem: its retained comparison and finite-free parameters are not
needed by the augmentation-only argument. No definitions, interfaces, attributes, other
existing modules, or unit routes changed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.IntegralFiniteScalar.finiteFreeScalarDerivedComparison_augmentation`
(node `lem-sfb-finite-free-scalar-derived-comparison-augmentation`).

No sorry remains in the item. Added zero holes and zero split-off statements.
The proof uses existing declared infrastructure; this does not claim that its transitive
import closure is free of sorry.

## No longer needed

No existing import was removed. The statement still needs
`Sheaf.Paper.IntegralFiniteScalarModelDefinitions`, whose imports retain the two-term
complex and augmentation constructions.

Removed from this node's proof dependencies:
- `lem-sfb-finite-free-mono-cokernel-kflat`: its finite-free/K-flat theorem is unnecessary;
  the generic canonical cone augmentation theorem suffices. Its module
  `Sheaf.Algebra.Homology.FiniteFreeMonoCokernelKFlat` still supplies the constructions
  through the model definitions and is not withdrawn or globally pruned.
- `lem-pe-internal-section-tensor-comparison`: neither section-module transport nor tensor
  comparisons occur in this proof. Its module
  `Sheaf.CategoryTheory.InternalSectionTensorComparison` is not needed as a proof import
  here; no claim is made that other consumers no longer need it.

No module was withdrawn. The unit's resolution step is preserved.

## Where the brief, the DAG or earlier work was wrong

The planned finite-free mono-cokernel and section-tensor comparison route was needlessly
strong for the augmentation conjunct. Short exactness alone gives the canonical
augmentation quasi-isomorphism, and exact point pullback preserves it. The additional
parameters remain unchanged for caller compatibility. No statement is disputed.

The current server queue listed a proof item, not a rework repair, and had no item build-error
record. Read the direct consumer `FiniteFreeScalarDerivedComparisonFlatness`; its use of
the unchanged theorem requires no adaptation.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteFreeScalarDerivedComparisonAugmentation": "0a128c53e96c0c3937f4f6fc65adf423831b9c2e"}, "results": {}, "time": "2026-10-28T10:16:41+0800", "transitive": 0, "version": 1}
```

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
