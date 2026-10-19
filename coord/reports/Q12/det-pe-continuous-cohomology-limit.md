# Stage-1 report: det-pe-continuous-cohomology-limit

Files written:

- dag/nodes/sec-proetale-coefficients/det-pe-continuous-cohomology-limit.json: item, split; no Mathlib match for the full pro-etale statement.
- citations.json.

Attachments:

- No finished declaration in /home/ubuntu/weil-src-slopmaster2/WeilConjectures states the item or carries the blueprint tag.

WANTED:

- None.

I read coord/brief-stage1.md, stages/1-dag.md, SETUP.md, GOAL.md, coord/dag-sync.md, delivery-errors sections B–E, the chapter record dag/chapters/sec-proetale-coefficients.json, the unit record dag/units/sk-prop-pe-continuous-cohomology.json, the imported item, and the current blueprint files sk-prop-pe-continuous-cohomology-limit.md and .proof.md. The item statement agrees with the blueprint and was not changed. The source checkout has no declaration tagged (blueprint: det-pe-continuous-cohomology-limit).

## Not duplicates

- No new node was created. The categorical right-adjoint limit fact is already the Mathlib leaf lem-weil-pbc-right-adjoint-preserves-limits; the reviewed pro-etale module-sheaf comparison is det-pe-milnor-epimorphic.

## Review by Q12

Step 1 uses det-pe-milnor-epimorphic. I opened its full statement and checked that it assumes a sheaf of rings, a tower of module sheaves with epimorphic transitions, and concludes that the canonical ordinary-limit-to-derived-limit map is an isomorphism. Every abelian sheaf is canonically a module over the constant Z-sheaf, so the specialization has exactly the item’s hypotheses and conclusion. The statement’s indexing starts at zero while the item starts at one; reindexing the sequence is harmless and was made explicit in the step.

Step 2 uses lem-weil-pbc-right-adjoint-preserves-limits. I opened the existing Mathlib leaf and verified that its statement says a right adjoint sends any existing limit cone to a limit cone, so it supplies the countable-product comparison used here. I also opened det-pe-milnor-sequence, whose statement defines the Roos model as Cone(1-T)[-1], and checked that it applies to the constant Z-module tower. The derived-sections functor is the right adjoint in the derived global-sections adjunction, as asserted in the blueprint proof sentence. Applying it to the Roos triangle preserves the product terms and the shift map, so the resulting fibre is exactly the derived limit of the derived sections.

I searched the whole DAG and blueprint for continuous cohomology limits, Roos triangles, right-adjoint product preservation, and derived sections. The directly stronger pro-etale comparison is the reviewed sibling det-pe-milnor-epimorphic, used as a declared adjacent-unit tool. No new node was needed: the right-adjoint limit statement is already a Mathlib leaf, and it does not restate either clause of the item. I checked edge cases conceptually: a singleton tower, an eventually constant tower, an empty scheme/object, and degree-zero complexes all reduce to the ordinary limit/Roos calculation. No statement error or source error was found, no SGA source is used, and the proof dependencies equal the union of the step uses.
