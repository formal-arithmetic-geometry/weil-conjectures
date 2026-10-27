## What changed

Split the parent `flat_and_quotients` proof obligation into three named component
lemmas and combined them in the item theorem. The item theorem now compiles; the
three component proofs remain explicit stage-3 obligations.

## Proved and sorry left

Closed `CategoryTheory.ConstantCompletion.flat_and_quotients` by a real conjunction
proof from the three component declarations. Added three strictly smaller named
holes: `flat_and_quotients_flatness`, `flat_and_quotients_projection`, and
`flat_and_quotients_quotient`.

## No longer needed

None. The existing imports and the generic sectionwise adic-limit dependency remain
part of the planned route.

## Where the brief, the DAG or earlier work was wrong

The parent theorem combines three independent conclusions while its available
sectionwise adic-limit declaration is substantially larger than any one conclusion.
The delivery therefore decomposes the parent into the three mathematical components
rather than introducing an equivalent restatement.

## New nodes

`new-h2-constant-completion-flatness`, `new-h2-constant-completion-projection`, and
`new-h2-constant-completion-quotient`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionFlatAndQuotients": "2a480b27a0b0954e775bcd29ac3fa2c9268b0f6a", "Sheaf.Paper.ConstantCompletionFlatAndQuotientsFlatness": "0d3905fac4a6240d53dee7127e000c982de8e46d", "Sheaf.Paper.ConstantCompletionFlatAndQuotientsProjection": "c71ceb6f764bee08fc9e41bc8a17a34e54c5e821", "Sheaf.Paper.ConstantCompletionFlatAndQuotientsQuotient": "6a4d3f71a42df16d0ede093431bdbe3d93c8dc62"}, "results": {}, "time": "2026-10-28T00:18:33+0800", "transitive": 0, "version": 1}
```

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
