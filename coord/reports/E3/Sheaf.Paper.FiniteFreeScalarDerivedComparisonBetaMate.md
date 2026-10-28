## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralFiniteScalar.finiteFreeScalarDerivedComparison_beta_mate`
in its existing module, preserving the full signature and all imports. Three proved private
category-theoretic helpers identify the normalized conjugate with the geometric mate and
commute a Hom-adjunction transpose with restriction, and calculate the tensor projection. The supplied pullback square and beta
naturality at the counit then give exactly the defined scalar-first projection.

Updated the item's DAG proof and proof dependencies to match this direct formal argument.
No shared definitions, interfaces, instances, public imports, or other modules changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.IntegralFiniteScalar.finiteFreeScalarDerivedComparison_beta_mate`
(node `new-sfb-finite-free-scalar-derived-comparison-beta-mate`).
No holes added or split off. No `sorry` remains in the delivered module.
The single-file server compile succeeded in 9.8 seconds; its only formatting warning
was removed before delivery. The delivery tool checks the final source and its axioms.

## No longer needed

No import was removed: the sole public import supplies the statement's existing interfaces.
This proof does not need these former proof dependencies:

- `new-sfb-finite-free-scalar-derived-comparison-beta-normalized`
  (`Sheaf.Paper.FiniteFreeScalarDerivedComparisonBetaNormalization`): beta and its pullback
  square are hypotheses here, so their construction is not needed for the mate implication.
- `lem-sfb-kflat-scalar-comparison-normalization`
  (`Sheaf.Paper.KFlatScalarComparisonNormalization`): `D.thetaNormalization` already specifies
  the scalar mate, and Mathlib's iterated-mates identity suffices.
- `lem-weil-pbc-ring-sheaf-change-adjunction`
  (`Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`): the restriction/direct-image
  arrow used here is defined as a conjugate, so the generic mate-Hom identity applies directly.
- `lem-weil-pbc-ringed-projection-mate-exact`
  (`Sheaf.Paper.ProjectionMateExact`): the claim is equality of the defined projection arrow;
  exactness and shift compatibility play no role in this equality.

These dependencies may remain needed by other parents or by the public interface's import
closure; no withdrawal or claim of global module pruning is made.

## Where the brief, the DAG or earlier work was wrong

The old proof plan prescribed transport through section-module models and the general
ring-sheaf adjunction theorem. The displayed definitions make that detour unnecessary.
The normalization of `D.theta` and the existing Mathlib iterated-mates theorem identify the
specified conjugate directly. The augmentation normalization hypothesis is retained, but
this formal implication only needs beta's naturality and the displayed pullback equation.

The generic identities are valid for arbitrary categories and adjunctions; the final tensor
calculation uses only bifunctoriality and cancellation of beta's isomorphism. Thus zero
rings, zero complexes, empty schemes, and non-flat coefficient maps require no extra cases.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteFreeScalarDerivedComparisonBetaMate": "64e3b92acd4ea9a5de3b5607eab7e584c51e8171"}, "results": {"Sheaf.Paper.FiniteFreeScalarDerivedComparisonBeta": {"hash": "9b058f32f64c3eb31791c908846113e95d3498fc", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T10:30:00+0800", "transitive": 0, "version": 1}
```

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
