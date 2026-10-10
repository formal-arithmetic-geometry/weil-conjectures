# Stage-1 report: def-pur-pseudo-coherent-complex

## Files written

- `dag/nodes/sec-picard-framework/def-pur-pseudo-coherent-complex.json`: item marked `split`; no new nodes.
- `citations.json`: empty because the item is a definition with no proof steps.

## Attachments

None. A search of both `weil-src-slopmaster2/WeilConjectures` and `weil-conjectures-slopmaster2/WeilConjectures` found no declaration tagged `(blueprint: def-pur-pseudo-coherent-complex)` or an equivalent pseudo-coherent-complex definition.

## WANTED

None. The Stacks source checkout used for verification is `/home/ubuntu/c1-stacks-review/perfect.tex`, containing Tags 08FT and 08G5.

## What was checked

The copied node was checked against the Stacks definition in Tags 08FT and 08G5. It correctly states that for a scheme Y, an object E of D(O_Y) is pseudo-coherent when locally it is quasi-isomorphic to a bounded-above complex of finite free O_Y-modules, and records the equivalent Stacks formulation. The statement dependencies `def-pc-scheme` and `def-pc-derived-category` define the two notions used in the statement; no other notion is introduced. Since this is a definition, there are no proof steps, proof dependencies, or citation quotes.

Mathlib searches were run twice in the required search families. LeanFinder returned only unrelated finite-presentation/quasi-coherence and derived-category t-structure declarations; Loogle returned derived-category t-structure declarations and no `PseudoCoherent`; source grep returned no `pseudo.?coherent|PseudoCoherent` declaration. Thus this project-level definition is not a Mathlib leaf. Small edge checks (a point scheme and a bounded-above finite-free complex) agree directly with the definition.

## Review by H1

I read the item and its dependencies, then read the Stacks source for Tags 08FT and 08G5. The source and statement agree clause by clause: the ambient scheme, derived-category object, local quasi-isomorphism, bounded-above indexing, and finite-free terms are all present. No proof step cites any node, so `citations.json` is necessarily empty and there are no hypotheses to verify in a proof. I searched the whole DAG and blueprint for the tags and the defining phrase; no duplicate node or alternate blueprint statement was found. I also searched the Lean project checkouts by item id and pseudo-coherence keywords; no declaration exists. The only correction was changing the copied node from `unsplit` to `split` and replacing the inherited, proof-oriented blueprint place with the definition's actual source place.

## Second reading by H1

- Item statement: checked against `perfect.tex`, Tags 08FT and 08G5, hypothesis by hypothesis; verdict: correct definition of pseudo-coherence for an object of `D(\mathcal O_Y)` on a scheme, with the local bounded-above finite-free characterization.
- Proof steps: none; verdict: no proof argument or citation dependency is required for this definition item.
- New nodes: none; verdict: no subordinate statement was introduced, so B1-B7 and duplicate-node checks are vacuous.
- Dependencies: checked `def-pc-scheme` and `def-pc-derived-category`; verdict: both notions used by the statement are defined by those nodes.
- Edge cases: checked a point scheme, the zero complex, a bounded-above finite-free complex, and the empty scheme; verdict: the definition behaves as stated in each case.
- Mathlib/Lean search: checked the recorded semantic, Loogle, and source-grep searches and the Lean source checkouts; verdict: no exact pseudo-coherent-complex declaration or blueprint duplicate was found.

Changes made in this second reading: no mathematical changes; retained the worker's `split` status, source, dependencies, empty proof and citations, and corrected the review record to document this audit. The delivery tool supplies maintainer-owned `created` metadata when materializing the existing item node.
