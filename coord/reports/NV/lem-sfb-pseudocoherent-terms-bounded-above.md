# lem-sfb-pseudocoherent-terms-bounded-above

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-pseudocoherent-terms-bounded-above.json`: split the existing statement in five steps, using existing nodes; Mathlib searches found no match.
- `citations.json`: nine verbatim statement quotations, covering every use in every proof step.
- `searches.jsonl`: actual searches recorded by msearch.py. No new nodes and no Mathlib leaves.

## Attachments

None. Searched the live `lean/WeilConjectures/` source by the item's blueprint tag and by pseudo-coherence, bounded-above complexes, and terms. The existing general approximation, shift and triangle declarations supply tools, not an exact declaration for this item. No sorry declaration is treated as a finished proof.

## WANTED

None. The proof and its inputs are in the local Stacks sources.

## Corrections and scope

The statement is unchanged and is precisely the final assertion of Tag 064Y, `lemma-complex-pseudo-coherent-modules`, in `literature/stacks-project/more-algebra.tex`. The imported item had no proof. I supplied the omitted finite induction and lower-tail argument, rather than creating a node restating the finite-length or fixed-degree clauses of this item. No source error or statement dispute was found.

Read GOAL.md, the chapter and unit records, the three blueprint levels in SETUP.md, and the current latest blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). This is a supporting commutative-algebra input on the inherited alteration/duality prerequisite chain, not a replacement of the unit route. `blueprint_refs.py ancestor` reports `None` for the imported created-item chain; the inherited explicit `from.place` and `via` are retained, rather than inventing an imported ancestor. `blueprint_refs.py search` for pseudo-coherent and pseudo.coherent found zero blueprint nodes. The whole-DAG searches located the existing generic tools, so no new node was necessary.

## Unfinished work

None at stage 1. No Lean files were written and no compiler or build tool was run.

## Not duplicates

No new nodes. Reused existing nodes for all-m approximation, shift by one, middle-vertex pseudo-coherence, and degreewise split derived triangles. The other 064Y references, notably `lem-sfb-finite-free-algebra-pseudocoherent-resolution` and `lem-sfb-pseudocoherent-algebra-scalar-restriction`, concern algebra restriction/resolutions, not a missing prerequisite requiring a new copy here.

## Review by NV

I read the complete statement and proof of Stacks Tag 064Y (`lemma-complex-pseudo-coherent-modules`). It explicitly reduces to a finite stupid truncation, inducts using Tag 064R, then uses Tag 064U for the final assertion. I also read `lemma-cone-pseudo-coherent` (064R), `lemma-pseudo-coherent` (064U), and the degreewise split sequence and distinguished triangle definitions in `derived.tex` (014I and 014Q), with the derived-category exact-sequence discussion. The commutative ring hypothesis of our item is stronger than the source's ring hypothesis, so it supplies every tool's ring hypothesis.

For step 1 I opened the statements of `lem-pc-ring-pseudo-coherent-iff-all-m` and `lem-pc-ring-m-pseudo-coherent-shift`. The former gives all integer approximation levels for each module in degree zero; the latter has exactly the equivalence needed to iterate shifts, including negative shifts by using the reverse implication. For the shift [-i], level m-i before shifting is level m afterwards. This uses the terms, not their cohomology: no coherence assumption on R and no unjustified finiteness of kernels is inserted.

For step 2 I opened `lem-weil-pbc-degreewise-split-derived-triangle`. Its statement applies to arbitrary cochain complexes in any abelian category, without boundedness or injectivity requirements. The explicit identity/zero degree splittings in the step satisfy its retraction, section and complementary-sum requirements; sections need not be chain maps. The quotient is precisely the single complex in degree c. I opened `lem-pc-ring-pseudo-coherent-distinguished-triangle`: its middle-vertex clause assumes the two outer vertices are m-pseudo-coherent and concludes that the middle is m-pseudo-coherent. These are exactly the inductive hypothesis and step 1. The induction starts at the actually zero tail T_(b+1) and has finitely many steps down to m-1. The zero witness is justified by the statement of `def-pc-ring-m-pseudo-coherent`, also opened.

For step 3 I checked the quotient at the cutoff: it vanishes in degrees at least m-1, even though its top surviving term may have new cohomology in degree m-2. Hence every cohomology in degree at least m vanishes and the zero map has exactly the isomorphism/surjection requirements stated in `def-pc-ring-m-pseudo-coherent`. This is a direct check from the definition, not an uncited transfer theorem for truncation.

For step 4 the same degreewise-split triangle node applies to T into C with quotient L: the splittings are displayed, and there is no claim of a splitting as complexes. The same middle-vertex clause applies at the same integer m; no rotation or off-by-one approximation is assumed. Step 5 invokes the reverse implication of the all-m node for the original complex C, precisely the final finite-free-model conclusion. I copied a verbatim piece of each cited statement into citations.json and checked the quotations against the current files.

I tested zero complexes, the zero ring, complexes supported in one arbitrary degree, m-1>b (empty upper tail), and complexes unbounded to the left. In the last case only the upper truncation is used for finite induction, and the entire unbounded lower quotient has the zero approximation in the relevant degrees. Thus no unmentioned bounded-below hypothesis appears. All five steps are below 2000 characters; no long step hides a separate comparison lemma. The generic off-unit tools are declared in split_report.tool_uses.

Against delivery-errors B to E: there are no new-node form or duplicate issues; every non-elementary ingredient is an existing node with a statement saying what is used; the finite induction, its base, and its descent range are written out; the lower-tail approximation is checked explicitly; the proof does not shift the conclusion into another node. Mathlib searches ran through msearch.py with two natural-language phrasings, Loogle, LeanSearch and grep. I read their returned types: projective resolutions, K-projectivity, derived support and Grothendieck properties do not supply finite free approximations or this theorem.
