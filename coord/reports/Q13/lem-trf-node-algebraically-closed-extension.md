1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-node-algebraically-closed-extension.json` — statement node, split; no Mathlib match.
- `citations.json` — verbatim citation quotes for every proof-step dependency.

2. Attachments: none. No finished declaration bearing this statement or its blueprint tag exists in the read-only slopmaster2 source.

3. WANTED: none. The cited Stacks source and all DAG dependencies are present locally.

4. The imported node was an unsplit statement-only repair from the semistable-base-change review. I checked the statement against Stacks Tag 0C56 and kept all hypotheses, including the empty-scheme allowance and the absence of quasi-compactness, separatedness, and dimension assumptions. I audited the affine fibre-product and completed-local-ring statements used by the proof. Step 1 reduces a nonsmooth geometric point to a nonsmooth closed point downstairs using smooth base change and the residue field of the assumed completion. Step 2 identifies the unique point over that closed point in an affine scalar extension. Step 3 applies the existing `lem-trf-separable-closed-point-formal-presentation` with the presentation `k[[u,v]]/(uv)` to obtain `Ω[[u,v]]/(uv)`. Step 4 records the empty and pointwise cases. The only off-unit generic tool is `lem-pc-proper-base-change`, used solely for smoothness stability under arbitrary base change and declared in `split_report.tool_uses`. No new node was needed, and no duplicate or Mathlib leaf exists.

5. What I could not finish: nothing. The dry run is the remaining required delivery check.

## Review by Q13

I read `literature/stacks-project/curves.tex` at Tag 0C56 and its cited completed-local-ring comparison (Varieties Tag 0C54), and read the full statements of every node cited in the four steps. I verified that Step 1 uses only the smooth-base-change clause of `lem-pc-proper-base-change`, the finite-type definition, and the residue field preserved by completion; the node completion is exactly `k[[u,v]]/(uv)`. In Step 2 I checked the affine fibre-product isomorphism and the kernel description of the unique point over the `k`-rational closed point. In Step 3 I checked that the formal-presentation node applies because the residue field is `k`, the extension is `k\subseteq\Omega`, and its conclusion is stated for every presentation, so the chosen relation `uv` can be transported coefficientwise to `Ω`. Step 4 is the vacuous empty case and the pointwise universal quantifier. I ran fresh LeanFinder, Loogle, grep, and LeanSearch searches with the item id; their actual outputs are recorded in `searches.jsonl` and the node's `mathlib_searches`, with no matching Mathlib theorem. The statement, blueprint ancestry, source place, and proof dependencies are unchanged except for completing the split and adding the review/tool-use metadata.
