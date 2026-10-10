Files written:

1. `dag/nodes/sec-picard-framework/lem-pc-field-extension-surjective.json` — item, statement split with no new nodes; Mathlib searches found no packaged exact theorem.
2. `citations.json` — verbatim citations for the sole proof step.

Attachments: none.

WANTED: none.

What changed: the item now has one proof step, proof dependencies, `proof_origin`, the affine-spectrum statement dependency, and the required `split_report`. No new node was needed because the argument uses existing definition nodes.

What could not be finished: nothing.

## Review by E1

I read the item source context in Stacks Algebra (the statement that a field spectrum has one point and that the map induced by a field extension is surjective), the ancestor blueprint proof for `lem-pc-very-ample-descends`, and the existing surrounding node `lem-pc-field-extension-fpqc-cover`. I also read the statements of `def-pc-field-extension`, `def-weil-affine-spectrum`, and `def-weil-surjective-morphism`. The sole step cites exactly those statements: the field-extension definition supplies the inclusion and field hypotheses; the affine-spectrum statement explicitly says that the spectrum of a field has one point and that the ring map induces the spectrum morphism; and the surjective-morphism definition says surjectivity is surjectivity of the underlying point map. Thus the unique point maps to the unique point, proving the claim. I verified the hypotheses for both fields and tested the edge case `K = k`, where the morphism is the identity on a one-point spectrum. The Mathlib search record was retained from the item and found no declaration packaging this exact scheme-level assertion. I corrected the initial edit's JSON escaping by doubling every TeX backslash and added the required verbatim citation quotes.
