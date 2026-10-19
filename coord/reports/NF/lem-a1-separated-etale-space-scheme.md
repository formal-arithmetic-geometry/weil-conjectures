Files written:

- `dag/nodes/sec-purity-real-sheaves/lem-a1-separated-etale-space-scheme.json` — statement split, four proof steps.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-etale-space-locally-quasi-finite.json` — statement node, Mathlib no-match.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-separated-locally-qf-space-representable.json` — statement node, Mathlib no-match.
- `citations.json` — verbatim citations for every proof-step dependency.

Attachments:

- None.

WANTED:

- None. The cited Stacks source is present in `literature/stacks-project/spaces-morphisms.tex`.

What was wrong or changed:

- The imported item had no proof and was unsplit. The source gives two distinct non-elementary inputs, Tags 03XU and 03XX, so I created one statement-only child node for each rather than restating the item as a single child.
- I searched the whole DAG and both blueprint snapshots for the two tags and their key phrases; no duplicate node or blueprint statement was found.
- The item statement is unchanged, including the absence of quasi-compactness assumptions.
- Mathlib searches for both new nodes found only scheme-level étale and locally-quasi-finite declarations, with no algebraic-space theorem; all four required searches for each node are recorded in the corresponding `searches.jsonl`.

## Not duplicates

lem-a1-etale-space-locally-quasi-finite vs lem-a1-separated-etale-space-scheme: the new node states only the intermediate implication from chartwise étaleness to chartwise local quasi-finiteness for an arbitrary algebraic-space morphism; the item additionally assumes a closed diagonal and concludes scheme representability and étaleness.

lem-a1-separated-locally-qf-space-representable vs lem-a1-separated-etale-space-scheme: the new node is the general 03XX representability theorem for a chartwise locally quasi-finite, separated algebraic space over any scheme; it does not assume étaleness or conclude that the representing morphism is étale, which are the item’s extra conclusion.

What could not be finished:

- Nothing. This is a stage-1 natural-language split; no Lean source was written and no compiler or build tool was run.

## Review by NF

I read the item source at Stacks Tags 03XU and 03XX in `spaces-morphisms.tex`, including the surrounding schemehood section, and checked the item statement against those hypotheses. I also read the existing chartwise étale node (`lem-trf-space-chartwise-etale-permanence`) and the definitions of closed immersion and separated morphism used in the proof. The two new nodes are strictly broader inputs: the first only concludes chartwise local quasi-finiteness from chartwise étaleness, while the second concludes representability from chartwise local quasi-finiteness and a testwise closed diagonal, without assuming étaleness.

Step 1 cites the exact conclusion of the 03XU node and uses the item’s chartwise étale hypothesis. Step 2 cites the separated-morphism definition and the closed-immersion definition; I verified that the item’s “every scheme base change” wording is exactly the algebraic-space testwise interpretation needed for the diagonal condition. Step 3 cites the exact 03XX conclusion and instantiates its base scheme and target scheme both to `X`, preserving the map over `X`. Step 4 cites the existing source-scheme equivalence “chartwise etale is equivalent to representable etale”; I checked that transport along the representing isomorphism uses only the composition/isomorphism clauses already in that node. Every citation quote in `citations.json` is copied verbatim from the cited statement, and all proof dependencies are listed in `proof_deps`.
