Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-proj-tilde-functorial.json`: statement node, no new Mathlib leaf.
- `citations.json`: seven verbatim citations covering all proof-step uses.

Attachments:

- None.

WANTED:

- None; the cited Stacks source is named in the item and proof steps.

What was wrong or incomplete:

- The imported item had no proof and was marked `unsplit`; its `created.item` metadata points to the preceding sheafification item and was preserved as imported history. No statement change was needed.
- No matching declaration or blueprint duplicate was found for this functoriality statement.

What remains unfinished:

- Nothing in this stage. The proof uses existing off-unit infrastructure as declared in `split_report.tool_uses`; those statements are not duplicated here.

## Review by E1

I read the item's source reference, Stacks Constructions Tag 01M7 (label `lemma-proj-sheaves`) and the construction before Definition 01M6, and checked the imported statement against the displayed standard-open and stalk formulas. I searched the slopmaster2 source for the item tag, its Proj/tilde terminology, and likely declaration names; no declaration with this statement was present, so there is no attachment.

Step 1 cites the existing sheaf-existence statement for the identifications on `D_+(f)` and the graded-localization restriction statement for the fraction and semilinearity calculation; those statements explicitly provide the required sections and formula. Step 2 cites the same localization statement's identity and transitivity clauses; the remaining equality is the direct application of the degree-preserving map to a numerator. Step 3 cites the standard-open basis statement, the basis-extension theorem's unique compatible morphism clause, and the sheaf-existence statement; their hypotheses supply a basis closed under intersections, finite refinements, and the two sheaves with the prescribed module sections. Step 4 cites the sheaf-existence statement's stalk identification and checks that the local fraction formula sends the representative `y/h` to `phi(y)/h`.

I searched the DAG and blueprint for an existing functoriality node before editing; the only relevant nodes are the generic Proj sheaf, localization, basis, and basis-extension interfaces cited above. I recorded each cited sentence verbatim in `citations.json`, checked that every `uses` id is in `proof_deps`, and declared the four off-unit statements as generic tool uses because this unit's route consumes them as interfaces.
