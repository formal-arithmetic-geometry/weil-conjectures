## What changed

Added the proof-only import `Sheaf.Paper.ConstantAdicQuotientModelRealizationReduction`.
The assigned theorem now composes the geometric reduction isomorphism with the
inverse of the supplied lower model isomorphism.  Added the split-off reduction
theorem in its own module; its proof is the remaining geometric transport from
the upper tower level to the lower one.

## Proved and sorry left

The assigned declaration
`AlgebraicGeometry.Scheme.constantAdicQuotient_model_realization_extension_iso`
is proved by categorical composition.  One strictly smaller statement remains:
`AlgebraicGeometry.Scheme.constantAdicQuotient_model_realization_reduction`, in
node `lem-weil-pbc-constant-adic-quotient-model-realization-reduction`, whose
proof is left as `sorry`.

## No longer needed

No proof-dependency import was removed.  The target proof uses only the new
reduction theorem and the supplied lower model isomorphism; the scalar,
tower-normalization, and constant-realization dependencies are retained by the
split-off theorem.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the geometric transport and the final cancellation
against the supplied lower model.  The final cancellation is elementary once
the transport is isolated, so the geometric transport is delivered as one
strictly smaller theorem for parallel proof.

## New nodes

`lem-weil-pbc-constant-adic-quotient-model-realization-reduction` is realized by
`lean/Sheaf/Paper/ConstantAdicQuotientModelRealizationReduction.lean` and records
the upper-to-lower geometric reduction before the lower model is introduced.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstantAdicQuotientModelRealizationExtensionIso": "995b8b410da2a7728956121e0396058ebab18ded", "Sheaf.Paper.ConstantAdicQuotientModelRealizationReduction": "8bd8b14e1ec5e394550e7bab4ce41ed6160a422e"}, "results": {}, "time": "2026-10-28T06:24:25+0800", "transitive": 0, "version": 1}
```

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
