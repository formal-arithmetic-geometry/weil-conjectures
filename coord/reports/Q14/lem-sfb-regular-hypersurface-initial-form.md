## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-regular-hypersurface-initial-form.json`: statement item, now split into seven steps; full statement is not in Mathlib. No new nodes and no new Mathlib leaves.
- `citations.json`: ten step/node entries quoting the cited statements verbatim.
- `searches.jsonl`: actual msearch log for the item; inherited searches and their results were retained in the node.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, regular hypersurfaces, initial forms and the regular-graded terminology found no declaration giving every clause. The homogeneous-independence and regular-generator results cover ingredients, not the item.

## WANTED

None. The Stacks algebra source is present.

## Problems found and changes

The item was unsplit, without an earlier sandbox node or report and without a released repair note. Its statement is correct, including without completeness or equicharacteristic hypotheses. I changed no statement or statement dependency. The proof writes out the quotient map and its kernel in each degree, rather than assuming that passing to associated graded commutes with an arbitrary principal quotient.

The inherited blueprint provenance has `from.node = null`; `tools/blueprint_refs.py ancestor` independently reports `None`. I retained that inherited value and its exact place/via chain. The current source in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md` has replaced the old alteration discussion by the compactification/direct-image route. This is a local-algebra prerequisite of the existing nodal-chart item, and the split proves that item’s exact present dependency, without changing any chapter or unit route. Blueprint searches for regular graded, 00NO, 00KW, hypersurface and regular sequence produced no blueprint node stating this full result.

The semantic searches returned Weierstrass preparation, homogeneous localization and the analytic tangent cone, which do not state this result. A second leanfinder phrasing returned the principal nonzerodivisor dimension-drop theorem, already represented by `lem-weil-pbc-dimension-quotient-nonzerodivisor`; it does not give the associated-graded calculation. Loogle and the required source grep returned no hits. No searches were fabricated, and no new node was needed.

## Not duplicates

No new nodes. Reused `lem-weil-pbc-regular-local-generators-regular-sequence` and `lem-pur-regular-sequence-graded-polynomial` instead of creating a 00NO leaf; reused the existing Krull-intersection and 00KW nodes instead of restating them. The existing hypersurface criterion only gives the forward implication and is unnecessary here: the proof derives both directions from the explicit cotangent dimensions.

## Review by Q14

I read Stacks `algebra.tex` at 00NO (`lemma-regular-graded`), 00NP (`lemma-regular-domain`), 00NQ (`lemma-regular-ring-CM`), 00LN (`lemma-regular-quasi-regular`), 00IP (`lemma-intersect-powers-ideal-module-zero`), 00IQ (`lemma-intersection-powers-ideal-module`), 00KW (`lemma-one-equation`), and the cotangent calculation in 00NR (`lemma-regular-quotient-regular`). I also read the current blueprint’s direct-image proof, the chapter and unit records, and all ten cited node statements. This is an agent assembly using those sources; the graded principal-kernel computation is written explicitly. There are no new nodes requiring independent sources.

Step 1 uses precisely the regular-generator node’s assertion that every given minimal generating system is a regular sequence, and the graded-polynomial node’s canonical graded isomorphism with its specified variable images. Substitution is R=A, J=m, quotient k; the statement of that node includes the monomial bases, hence also the degree-one basis. These are generic algebra tools from other units, declared in split_report.tool_uses.

Step 2 uses the intersection node’s actual Jacobson-radical version, not merely a definition of separatedness. A is Noetherian, M=A is cyclic, and m is the Jacobson radical of a local ring. The least failed power gives the finite order and its uniqueness. Since f lies in m, its order is at least one.

Step 3 cites the graded-ring definition only for its explicit homogeneous multiplication formula. It proves the additional assertion it needs: lexicographic leading monomials over the residue field cannot cancel, and the product of the two initial classes is therefore nonzero. This proves order additivity in a few lines from step 1 and the formula; it does not leave an uncited domain or initial-ideal theorem. Step 4 uses that same formula and the already proved additivity. I checked the zero coefficient case, degrees q<e, q=e, and q>e separately in the written kernel computation: for q<e any af has order at least e, so its degree-q class vanishes; for q>=e the coefficient belongs to m^(q-e). Products and sums lift under the quotient by definition. Step 5 cites no node: summing homogeneous components identifies the kernel ideal and gives the bijection by representatives, while extending one nonzero vector to a basis computes the degree-one dimension. This is an elementary finite-dimensional calculation, not a new lemma in disguise.

Step 6 uses the domain node solely for absence of zero divisors in A, the nonzerodivisor dimension node with exactly its Noetherian/local/nonzerodivisor hypotheses, the local-quotient node with (f) contained in m, and the surjective-image node for Noetherianity of B. It explicitly identifies B/n with k; it does not assume a coefficient field embeds in A. Step 7 applies the cotangent-dimension node to this now established Noetherian local ring B, using its exact regularity-if-and-only-if clause. The numerical dimensions from steps 5 and 6 give e=1, which is exactly f not in m^2.

I checked delivery-errors B1–B10, C1–C8, D1–D5, E1–E7 against this split. There are no statement-only new nodes to hide the conclusion, no use of a cited node’s proof instead of its statement, and no source-only non-elementary invocation: every outside theorem is a cited existing node. All proofs are below 2000 characters per step. Every citation has its exact complete statement in citations.json. I tested A=k (no admissible nonzero f in m, so the hypotheses are empty), A=k[t]_(t) with f=t and f=t^2 (B dimension zero, cotangent dimensions zero and one), and the mixed-characteristic DVR A=Z_(p) with f=p and f=p^2. In dimension two, f=x gives a regular quotient, while f=x^2 and f=xy give cotangent dimension two and quotient dimension one. These cases check both orders and the need for f nonzero; f=0 is excluded because it has no finite order and would invalidate the dimension drop. No SGA source, Lean write, compiler, Lake command or repository write was used.

## Unfinished work

None for the one-level split. The inherited provenance is reported above rather than silently replaced. The required server preflight and dry run are the remaining validation before push.
