# Worker report

Item: lem-sfb-m-pseudocoherent-algebra-scalar-restriction. Group Q40, stage 1, 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-m-pseudocoherent-algebra-scalar-restriction.json: statement, split; no Mathlib match. Seven proof steps, no new nodes, no Mathlib leaves added. The statement, statement dependencies, source and inherited blueprint place/via are retained.
- citations.json: a verbatim statement quote for every node cited by every proof step.
- searches.jsonl: the search command's actual records for this item; its five fresh queries were added to the existing Mathlib searches without deleting the predecessor's search evidence.
- report.md: this report.

The sandbox initially contained no item or report, so the current repository item was used. There is no repair note for this item. No repository or launcher file was written, no git command was run in the read repository, and no Lean, compiler or build tool was run.

## Attachments

None. Searched lean/WeilConjectures for the exact item tag/id, pseudo-coherence keywords, and restriction/pseudo-coherence combinations. The project has pseudo-coherence definitions, triangle closure and finite top cohomology declarations, but no declaration stating the fixed-m equivalence under these hypotheses. A related full pseudo-coherence result in the DAG does not state the fixed-m theorem.

## WANTED

None. All sources needed for the proof are present.

## Problems found and choices made

The imported item was statement-only. Its statement is exactly the fixed-m equivalence in Stacks Tag 064Z, label lemma-finite-push-pseudo-coherent, in literature/stacks-project/more-algebra.tex; no statement dispute or correction is needed. Its explicit absence of a boundedness assumption is correct: whenever either side holds, a cohomological upper bound follows from its bounded approximation.

The forward argument follows 064Z. For reflection I retained its upper-degree induction but used Tag 064S to choose finite generators of top cohomology and lift them directly to cycles. The one-degree finite free T-complex so obtained replaces the source's induced E tensor T map and makes a Tor spectral sequence unnecessary. This is an agent refinement, marked proof_origin.by = agent. It is not an alternative route through a geometric theorem: it is the elementary top-approximation construction inside the same ring-algebra argument.

I used a chosen upper bound rather than a largest nonzero cohomology degree, so the acyclic case needs no exception. The cone is m-pseudo-coherent over S because its first vertex is (m+1)-pseudo-coherent, not merely m-pseudo-coherent. That extra degree is available from pseudo-coherence of T over S and the bounded-above terms lemma.

Read the chapter record, the unit record, and the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The inherited place is the algebraic prerequisite below direct-images (3), via Tag 0673. tools/blueprint_refs.py ancestor reports None for this already-existing created-node chain. I preserved its inherited null from.node and the detailed place/via rather than inventing an ancestor. Whole-blueprint searches for 'pseudo-coherent' and 'scalar restriction' found no imported blueprint statement; whole-DAG searches by tags and concepts found all the reused lemmas.

## Not duplicates

No new nodes were created. The existing lem-sfb-pseudocoherent-algebra-scalar-restriction states the full pseudo-coherent equivalence; applying it does not establish a fixed-m equivalence. The existing lem-sfb-pseudocoherent-terms-bounded-above already supplies precisely the Tag 064Y input, so it was reused. The existing triangle and finite top cohomology nodes already supply the other non-elementary inputs.

## Review by Q40

I read Stacks more-algebra.tex, lemma-finite-push-pseudo-coherent (064Z) completely, together with definition-pseudo-coherent (064Q), lemma-cone-pseudo-coherent (064R), lemma-finite-cohomology (064S), lemma-pseudo-coherent (064U), lemma-recognize-pseudo-coherent (064W), and lemma-complex-pseudo-coherent-modules (064Y). I checked the labels against literature/stacks-project/tags/tags. There are no new nodes needing separate source reviews. I also read the statement of every node cited, not merely its proof or title.

Step 1 cites def-weil-abstract-derived-category for localization, cohomology, shifts and the cone description of distinguished triangles, and def-pc-ring-pseudo-coherent-complex for the actual bounded-above finite free S-model of T. Keeping the groups and differentials proves preservation of kernels, images, quasi-isomorphisms and cones directly. Finite direct sums of that model compute their kernels and images coordinatewise and model restricted finite free T-modules. This is an explicit elementary construction, not an appeal to a hidden finite-sum theorem.

Step 2 uses lem-sfb-pseudocoherent-terms-bounded-above, whose statement requires a termwise bounded-above complex of pseudo-coherent modules. Here the complex is bounded and each term has the model from Step 1, so these hypotheses hold. lem-pc-ring-pseudo-coherent-iff-all-m states exactly the all-cutoffs implication used. The identity approximation over T is an instance of def-pc-ring-m-pseudo-coherent.

Step 3 uses that approximation definition, TR1 of def-weil-triangulated-category to complete its derived morphism, and lem-sf-derived-homology-long-exact to show that its cone has zero cohomology at every i >= m. I checked the critical endpoints: H^m(alpha) is onto and H^(m+1)(alpha) is injective. The zero complex therefore witnesses m-pseudo-coherence of the restricted cone. The middle-vertex clause of lem-pc-ring-pseudo-coherent-distinguished-triangle applies with both outer vertices m-pseudo-coherent over S, exactly as its statement says.

Step 4 uses only def-pc-ring-m-pseudo-coherent and Step 1. A bounded witness supplies an upper bound for cohomology above m. The induction assertion quantifies over every L with upper bound n and restricted m-pseudo-coherence; its natural parameter n-m+1 has base n=m-1. The zero witness proves that base. This does not assume boundedness of L as a complex or any lower bound.

Step 5 cites the same approximation definition to pass from cutoff m to cutoff n >= m, and lem-sc-finite-cohomology with R=S and m there equal to n here. Its vanishing assumption holds in all degrees above n, and its conclusion is finite type over S, not an unjustified finiteness claim about arbitrary lower cohomology. S-generators are T-generators because the actions compose through f. Choosing cycle representatives defines a T-linear chain map from T^r[-n] with zero differential, with a surjection on top cohomology. Every part after the cited finiteness theorem is written out.

Step 6 uses the cone description in def-weil-abstract-derived-category and the exact sequence stated in lem-sf-derived-homology-long-exact. At n the top surjection and the vanishing next cohomology of E kill H^n(C); above n the adjacent groups vanish. Thus the induction applies at n-1, rather than at an unchanged bound.

Step 7 uses both clauses actually present in lem-pc-ring-pseudo-coherent-distinguished-triangle. Over S, its first clause requires (m+1)-pseudo-coherence of f_*E and m-pseudo-coherence of f_*L; Step 2 and the induction hypotheses give them. Over T, its middle clause requires m-pseudo-coherence of E and C, supplied by the identity witness in def-pc-ring-m-pseudo-coherent and the induction hypothesis. The two rings are kept distinct throughout.

I reviewed delivery-errors B through E point by point. There are no new statements to hide a proof in, no undefined new notions, no restatement nodes, and no new same-tag pairs. Every non-elementary input is an existing cited statement, and citations.json copies it verbatim. The four generic off-unit tools (all-cutoffs characterization, triangle closure, long exact cohomology, finite top cohomology) are declared in split_report.tool_uses with their roles; they do not replace the unit route. No SGA source is cited. Each step is below 1000 characters, so none exceeds the 2000-character review threshold.

Small cases checked: the zero complex and acyclic complexes use upper-bound induction without a highest nonzero degree; the zero ring and the zero algebra have only zero unital modules; r=0 is allowed for all finite sums and cycle lifts. For n=m, the cone drops to the zero-witness base n=m-1 with no off-by-one. For n>m, the witness is onto in degree n because it is an isomorphism there. The notation [-n] puts the free module in degree n under the stated shift convention. Arbitrarily nonfinite cohomology below m is permitted. No flatness is used; for example Z to Z/2 satisfies the algebra hypothesis although it is not flat. Neither a Noetherian hypothesis nor finiteness of kernels over a noncoherent ring was used.

The five fresh Mathlib queries were run through msearch.py and their hits read. Loogle and the source grep had zero hits for pseudo-coherence. LeanFinder returned general restriction pseudofunctors, cohomological support bounds, and ordinary finite-presentation results. LeanSearch returned preservation of homology by exact functors and general restriction/complex constructions. None states the fixed-degree finite-free-approximation equivalence or a one-line specialization. A second semantic phrasing was tried; the earlier item's search evidence was retained.

## Unfinished work

None in this stage-1 split. No new nodes need a later split. Formal Lean proofs are outside this task.
