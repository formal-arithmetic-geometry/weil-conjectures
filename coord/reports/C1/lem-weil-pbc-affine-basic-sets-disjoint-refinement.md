# Worker report: lem-weil-pbc-affine-basic-sets-disjoint-refinement

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-basic-set-difference.json` — statement node (unsplit): for two basic subsets of `Spec A`, the difference is a finite pairwise-disjoint union of basic subsets. It gives the explicit pieces `D(f) ∩ V(G,h)` and `D(f h k_j) ∩ V(G,k_1,…,k_{j-1})`, and records LeanSearch, LeanFinder, and Mathlib-source grep searches with no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-basic-sets-disjoint-refinement.json` — split the finite-family refinement statement by induction, using the difference node. The empty family is handled explicitly. Existing provenance (`created.item`) was preserved because this item node was created by the parent split.

## Attachments

None.

## WANTED

WANTED: `literature/stacks-project/etale-cohomology.tex`, Stacks Tag 03S0 (the refinement sentence in the proof), and `literature/stacks-project/algebra.tex`, Tag 0G1P (basic constructible sets), because the source TeX files are not present in this clone. The proof is therefore marked `proof_origin.by = agent`; tag-to-file/label evidence is recorded in `literature/stacks-tags-cited.tsv` and the node source fields.

## Review against delivery-errors B–E

- **B:** The new node is statement-only and self-contained: it introduces `A`, `Spec A`, `D`, `V`, and both basic sets, with an explicit `def-weil-affine-spectrum` dependency. TeX is escaped once in JSON. It is `unsplit`, has a source, and records all three required Mathlib search kinds. No duplicate node was found by searching `dag/nodes` for the item id and the basic-set/difference terminology.
- **C:** The item’s two proof steps cite only the statement of the new difference node; the induction and set-disjointness bookkeeping are written directly. The support node’s two steps use only the affine-spectrum setting and spell out membership cases, rather than appealing to the source tag as a proof.
- **D:** This is a genuine proof split: the support node is strictly smaller (difference of two basic sets), and the item performs finite disjointization by induction. No step is circular, and the empty case is included.
- **E:** For the difference formula, a prime is partitioned by whether `h` lies in it and, when not, by the least `j` for which `k_j` does not lie in it; this checks both coverage and pairwise disjointness. The finite-family induction maintains the invariant that the current pieces are pairwise disjoint and have union of the processed inputs. Small cases checked conceptually: `m=0`, `s=0`, and a one-set family.

## Checks

`python3 tools/check_dag.py` completed with no cycles (its existing reachability warnings are unrelated). `python3 tools/review_split.py lem-weil-pbc-affine-basic-sets-disjoint-refinement` passed: one new node, proof written by an agent.

## Unresolved

The support node remains unsplit because Mathlib has no matching theorem or direct `IsSetSemiring` instance for these affine basic subsets. The source TeX must be supplied later to replace the agent-written proof origin if required.

## Review by C1

The cited source locations are recorded as Stacks Tags 03S0 and 0G1P; the TeX files are absent in this clone, so I checked the node statement against the imported blueprint and the tag index and retained the worker's `WANTED` notice. The item states finite disjoint refinement of a finite family of affine basic sets, and the new difference node states the strictly smaller two-set difference used by the induction. Their hypotheses and objects are explicit, including the affine spectrum and basic-open/closed notation.

For the item proof, the empty-family base case and induction step use only the difference node plus finite set partition bookkeeping; the worker spells out the invariant and the singleton edge case. The support node's membership partition is the least-index decomposition and is not cited as an unproved tag. No step uses a node for facts absent from its statement, and there is no cycle. The new node is statement-only, has `status: unsplit`, source provenance, and all three required Mathlib searches; the duplicate search found no existing node for this difference statement. I checked small cases `m=0`, `m=1`, and an empty generating list. No hypothesis was introduced or dropped. The worker's B-E review was accepted; this lead review supplies section F.
