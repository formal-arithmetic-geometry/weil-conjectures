## What changed

The item module now imports three proof-only helper modules and constructs
`ScalarCompatibility` from their three field-level statements. The item theorem
`openQuotientScalarCompatibilityData` is proved by unpacking the finite and
strict-system witnesses and applying the evaluation compatibility theorem.

## Proved and sorry left

- Proved `openQuotientScalarCompatibilityData` by the structure constructor; its
  proof contains no `sorry`.
- Added the strictly smaller split statements
  `openQuotientScalarFiniteCompatibility`,
  `openQuotientScalarSystemsCompatibility`, and
  `openQuotientScalarEvaluationCompatibility`; each remains a named `sorry` with
  its own DAG node.

## No longer needed

No imports were removed. The item uses all three helper modules and the
`OpenTensorQuotientData` definitions.

## Where the brief, the DAG or earlier work was wrong

The existing node described the construction as one undivided descent argument,
while the Lean structure has three independent fields. The delivery records
those fields as separate, strictly smaller obligations and makes the packaging
proof explicit. No target statement or existing definition was changed.

## New nodes

- `lem-sf-open-quotient-scalar-finite-compatibility` records the finite comparison
  family.
- `lem-sf-open-quotient-scalar-system-compatibility` records the strict-system
  comparison.
- `lem-sf-open-quotient-scalar-evaluation-compatibility` records the coefficient
  evaluation equation for the two comparisons.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenQuotientScalarCompatibilityData": "fa58a3f9b4caf7ba11b0cde6c2a5747c2df0d191", "Sheaf.SixFunctors.OpenQuotientScalarEvaluationCompatibility": "6094e7367c5fb1222d20286eabb9cdd55d2d3716", "Sheaf.SixFunctors.OpenQuotientScalarFiniteCompatibility": "67073a17ecbc09d6a14b9b91f3018caaaeb75855", "Sheaf.SixFunctors.OpenQuotientScalarSystemsCompatibility": "0fceb2a8bad5cf960f924d503fe84d0416272cab"}, "results": {}, "time": "2026-10-28T04:21:03+0800", "transitive": 0, "version": 1}
```

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
