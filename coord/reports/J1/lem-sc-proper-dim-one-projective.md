# Worker report

Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-proper-dim-one-projective.json` — statement split, status `split`.
- `dag/nodes/sec-curve-estimates/lem-sc-dim-one-quasi-projective.json` — new unsplit statement node; Mathlib search found no match.

Attachments: none. No sorry-free slopmaster2 declaration states this item (the item has `lean_audit.slopmaster2.state = none`), and no declaration matching the tag or theorem wording was found in `WeilConjectures` or `Comparator`.

WANTED: none. The cited Stacks source is available through the local review checkout at `/home/ubuntu/c1-stacks-review/varieties.tex` and the online tag page.

The imported item had no proof steps. I expanded Lemma 0A26 into (1) the Tag 0A25 dimension-one quasi-projectivity input and (2) the properness/closed-image argument from Tag 01W6, followed by the existing immersion closed-image criterion. The new node is strictly smaller than the item and does not restate the conclusion. The existing imported node `lem-weil-pbc-proper-closed-image` is used as a tool; the other three auxiliary facts are accepted Mathlib leaves from their respective units. No source or statement error was found.

## Review by J1

Source checked: Stacks Project, Varieties, Lemma 33.43.4, Tag 0A26 (`literature/stacks-project/varieties.tex`, lines 9217–9231), together with Lemma 33.43.3, Tag 0A25, and Morphisms Lemma 29.42.7, Tag 01W6. The item statement matches 0A26: a proper scheme over a field with dimension at most one is H-projective, expressed as a closed immersion into some `P^N_k`. The new node matches 0A25: separated finite-type dimension at most one over a field admits a locally closed immersion into projective space. Hypotheses are preserved: properness supplies separatedness and finite type, and the dimension bound is unchanged.

Step 1 uses the definition of proper morphism for separatedness and finite type, then applies the new Tag 0A25 node. It is non-elementary because the quasi-projectivity theorem is the cited Stacks input.

Step 2 uses the accepted Mathlib leaves `lem-weil-pbc-projective-space-proj-separated`, `lem-weil-pbc-proper-over-separated`, and `lem-weil-pbc-immersion-closed-image-closed-immersion`, plus the imported tool node `lem-weil-pbc-proper-closed-image`. These statements provide, respectively, separatedness of projective space, properness of the immersion, closedness of its image, and conversion of an immersion with closed image into a closed immersion. The final projectivity conclusion is exactly the definition node `def-pc-projective-morphism`. No step is marked elementary.

The new node was searched against the whole DAG and blueprint before creation; no existing node states the general Tag 0A25 result. LeanSearch returned an HTTP 500, LeanFinder returned only generic Proj separatedness declarations, Loogle returned no quasi-projectivity theorem, and source grep found only the generic `IsQuasiProjective` predicate in `WeilConjectures`; the Mathlib source checkout is absent on this machine. The item itself was searched by LeanSearch, LeanFinder, Loogle, and source grep with no projectivity converse.

Small-case checks: the empty scheme (dimension `-\infty`) embeds as the empty closed subscheme of `P^0_k`; `Spec(k)` and finite zero-dimensional proper schemes are covered by the dimension-zero case and embed in projective space; the dimension hypothesis excludes higher-dimensional proper non-projective examples. The proof uses no algebraic-closedness or smoothness assumption.
