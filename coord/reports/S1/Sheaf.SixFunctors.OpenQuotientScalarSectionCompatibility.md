## What changed

Marked `openQuotientScalarSectionCompatibility` as `STATEMENT-DISPUTED`.
The theorem quantifies over an arbitrary natural isomorphism `finite`, but its
conclusion asserts the normalization equation for one particular comparison.
The proof hole remains open because the equation is not implied by the stated
hypotheses.

## Proved and sorry left

- No holes were closed.
- `openQuotientScalarSectionCompatibility` remains a named `sorry` recorded by
  node `lem-sf-open-quotient-scalar-section-compatibility`.

## No longer needed

None. The module keeps its declared import because the disputed statement uses
all definitions from `OpenTensorQuotientData`.

## Where the brief, the DAG or earlier work was wrong

The statement omits the required normalization hypothesis on `finite`. Given
one comparison satisfying the displayed equation, composing it with the
natural automorphism `-𝟙` of the target functor yields another isomorphism of
exactly the stated type. For odd `l` (take `l = 3`) and a nonzero coefficient
module and extension generator, the new comparison sends that generator to
its negative, so the displayed equality fails. The DAG proof plan also says
only “evaluate the finite comparison on the generator”; no hypothesis fixes
that evaluation. The intended statement needs either a canonical comparison
construction or an explicit generator-normalization field.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenQuotientScalarSectionCompatibility": "775f1e0ee7058cab105a5a2f4aa21e7a8f3cef17"}, "results": {}, "time": "2026-10-28T09:27:07+0800", "transitive": 0, "version": 1}
```

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
