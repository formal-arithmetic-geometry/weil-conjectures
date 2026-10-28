## What changed

Proved `AlgebraicGeometry.Scheme.constantAdicQuotient_realization_scalar_reduction`
in `Sheaf.Paper.ConstantAdicQuotientRealizationScalarReduction`, preserving its
signature, definitions and existing public imports. Added two proof imports:
`import all Sheaf.Paper.ConstantAdicQuotientScalarComparison` for its already
proved internal helpers, and `WeilConjectures.CategoryTheory.InverseMateEquivalence`.

The proof composes four isomorphisms: transport between the actual completion
quotients and the finite quotients of A; derived constant realization of the
consecutive finite quotient map; transport along the natural finite ring-sheaf
comparisons; and inverse image. The two transport mates are invertible because
the transverse functors are equivalences. The other two mates use existing
proved results. Exact derived compositors identify the resulting composite with
the two functors in the unchanged theorem statement. No additional boundedness,
flatness, nontriviality or geometric assumption is introduced. The argument also
covers n = 0 and zero quotient rings, since the coefficient bijectivity and
constant-realization results used have no nontriviality assumption.

Updated only this module's DAG proof, proof dependencies and proof origin to
record those four steps. Its unit's statement and route are unchanged.

The implementation compiled without errors or warnings using lcompile.py in
12.4 seconds before the final explanatory comments. The required deliver3.py
checks compile the final commented file and run the declaration/axiom probe.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.Scheme.constantAdicQuotient_realization_scalar_reduction`
(node `lem-weil-pbc-constant-adic-quotient-realization-scalar-reduction`).

Zero sorry remain in the item. Zero holes were added or split off. No other
existing declaration was modified.

## No longer needed

None: no import, module or node was pruned. Both original stated dependencies
remain needed. The proof uses the already proved internal coefficient-bijectivity,
constant scalar-mate and inverse-image scalar-mate helpers in
`ConstantAdicQuotientScalarComparison`, rather than reconstructing them or adding
another layer of obligations. No extra normalization, tower-model, stalk or
etale-effectivity module is imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The previous DAG contained one informal
pasting sentence; the updated proof spells out the consecutive finite quotient
square and the coefficient-system naturality equation needed to perform it.
The existing docstring calls this derived restriction, although the unchanged
Lean conclusion uses derived extension; the implemented proof follows that
conclusion. The actual map from each finite quotient to its completion quotient
is bijective, so the coefficient transport requires no additional hypothesis.
The current server queue row was checked: this is a proof item with one hole,
with no rework row or build-error record for this module.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstantAdicQuotientRealizationScalarReduction": "b3e279b78ad73d527607c3e10ce8f295bce1be9a"}, "results": {}, "time": "2026-10-28T10:11:59+0800", "transitive": 0, "version": 1}
```

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
