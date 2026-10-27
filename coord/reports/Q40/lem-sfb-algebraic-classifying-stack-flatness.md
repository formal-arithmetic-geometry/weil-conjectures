# Stage-1 delivery: lem-sfb-algebraic-classifying-stack-flatness

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-classifying-stack-flatness.json: item, split in five steps; statement and statement dependencies unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-quotient-flat-refinement.json: statement-only input, Stacks 06PJ; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-sheaf-surjective-property-descent.json: statement-only input, Stacks 06NR; no Mathlib match.
- citations.json: verbatim statement excerpts for every proof-step citation.

Two new nodes, zero Mathlib leaves. No Lean files written or compiler invoked. The sandbox initially contained only dispatcher marker files, with no previous split, report, or search log to continue.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, classifying-stack flatness, AlgebraicStack, classifyingStack, and gerbe, and for quotient/refinement and sheaf-surjectivity notions. There is no project declaration stating the item or either new input. The source's scheme/sheaf declarations do not supply algebraic-space or algebraic-stack assertions.

## WANTED

None. All proof sources are present in literature/stacks-project.

## What needed repair

The imported item had an empty proof. Its statement is correct: I read criteria.tex Tag 06PL, lemma-BG-algebraic, including the complete converse. There is no statement dispute. The source goes through the group-action criterion 06PK; I use its general groupoid criterion 06PJ directly for (B,G). This avoids an unnecessary action-groupoid comparison while preserving exactly the source's presentation, sheaf-surjection, and descent argument.

The important distinction is that the refinement B' -> B is only a surjection of fppf sheaves. Neither it nor the map R' -> G x_B B' can be assumed flat. The 06NR input descends the property of the *composite*, without such an assumption. The proof then chooses actual fppf scheme coverings on a scheme atlas before invoking the existing target-descent node. The empty-base case is included.

## Blueprint and searches

Read the chapter and unit records, SETUP's three levels, and the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, particularly (3). This is the inherited supporting neutral-gerbe branch; it does not alter that route or a unit's statement. The ancestor command reports blueprint.from.node = None for this inherited created-node chain. I retained its null ancestor and existing via list in the item, prepended the item for the two new nodes, and gave exact supporting places. No invented blueprint ancestor was assigned.

Searched the whole DAG by tags 06PL, 06PJ, 06PK, 06NR, 041T and 041W and by quotient-algebraicity, sheaf-surjectivity and composite-descent concepts; read the relevant node statements. Ran blueprint_refs.py search for classifying stack, 06PL, 06PJ, 06PK, 06NR, quotient algebraic, surjection sheaves, and groupoid refinement; all returned zero blueprint matches. The new ids do not exist in the read clone.

All new-node Mathlib searches ran through msearch.py, and searches.jsonl preserves their actual queries, results, and digests. Both new nodes have LeanFinder, LeanSearch, Loogle and grep searches, with two distinct natural-language phrasings each. Read all hits: they concern schemes, categorical groupoids, and locally surjective sheaves, not the required stack/space theorem. In particular the generic scheme DescendsAlong instance and the sheaf IsLocallySurjective_comp theorem are not the assertion of 06NR: they do not descend flatness or finite presentation of a composite through an arbitrary fppf sheaf epimorphism of spaces. Read Mathlib AlgebraicGeometry/Morphisms/FlatDescent.lean and AlgebraicGeometry/Sites/Representability.lean around the reported candidates. No source theorem is an exact match or one-line specialization. The item's earlier searches are retained, with this session's searches appended. No unrun query is recorded.

## Not duplicates

lem-sfb-algebraic-quotient-flat-refinement vs lem-sfb-flat-groupoid-algebraic-quotient: the existing theorem assumes the original arrow maps flat and locally finitely presented and proves algebraicity; the new input starts from algebraicity with unrestricted arrow maps and produces a suitable restriction. Neither states classifying-stack flatness.

lem-sfb-space-sheaf-surjective-property-descent vs lem-sfb-representable-fppf-etale-open-descent: the existing theorem descends a base-changed morphism along a flat locally finitely presented cover; the new lemma descends a property of a composite through a sheaf-surjective first arrow without flatness or finiteness of that arrow.

lem-sfb-space-sheaf-surjective-property-descent vs lem-sfb-representable-flat-lfp-fppf-descent: the latter likewise assumes the covering morphism is flat and locally finitely presented and uses a cartesian square; the new lemma has neither requirement, and also handles local finite type separately.

No existing node has source tag 06PJ or 06NR. The only live node with source tag 06PL is the item itself. No new node restates the item or one of its conclusions about G -> B: the first is a groupoid-presentation existence input and the second is a property-of-composites descent input. The proof still carries the local-lift, arrow-factorization, and final descent arguments.

## Review by Q40

I read Stacks criteria.tex lemma-BG-algebraic (06PL) for the item, lemma-quotient-algebraic (06PJ) with its proof for the presentation node, and spaces-descent.tex lemma-curiosity (06NR) with its proof for the composite-descent node. For the final descent I also read spaces-descent.tex lemma-descending-property-flat (041W) and lemma-descending-property-locally-finite-presentation (041T). These sources do not impose separation, quasi-compactness or Noetherian hypotheses here.

Step 1 uses exactly the new 06PJ statement. Its input is the algebraic quotient in the item's hypothesis, and its restricted arrow object is B' x_B G x_B B', since source and target of G agree. Both projections to B' have the two properties; no clause of 06PL was moved into that input.

Step 2 uses the existing algebraic-space fibre-product theorem for the displayed spaces. The rest is the elementary local-section argument: an h-lift supplies a g-lift, then a local g-lift of the common image of (a,b'_2) supplies the missing first coordinate. I explicitly checked the last projection is v composed with u. This is an elementary step from the cited product theorem and the sheaf-surjection definition; it hides no descent lemma.

Step 3 uses the 06NR statement twice, for two independent properties, with X=R', Y=G x_B B', Z=B'. Its hypotheses are the composite property from Step 1 and the sheaf-surjectivity from Step 2. The node explicitly requires no flatness of u, exactly what this application needs. Assuming g flat here would have made the proof circular; no such assumption remains.

Step 4 uses the chartwise calculus statement's arbitrary-base-change and open-source-locality clauses, and its smoothness of etale maps. I checked its domain carefully: algebraic spaces are discrete algebraic stacks because their sheaf descent, representable diagonal and etale atlas satisfy the cited definitions; the fibred-groupoid calculus expressly says maps between spaces are representable and etale maps are smooth. Thus the calculus applies to the spaces here. The algebraic-space definition supplies T -> B. The fppf-site definition supplies flatness, local finite presentation and joint surjectivity of T_i -> T. The set-indexed coproduct node supplies W, its clopen components and the glued map to B'. Open-source locality then checks W -> T; the two base-change maps of G are explicitly identified on test sections. This step does not confuse an arbitrary sheaf-surjective B' -> B with an fppf cover. The fixed universe contains the covering family and its coproduct.

Step 5 uses the algebraic-space clause of the existing representable-fppf-etale-open-descent node. The actual morphism W -> T has all three required covering hypotheses from Step 4. Its pullback of G x_B T -> T is the map already shown flat and locally finitely presented, with the fibre-product identification written on sections. The local-properties chart-test node is then applied first with identity target chart T -> T, and then with T -> B. Both applications require only etale surjective scheme charts and give the stated properties separately. This verifies precisely the chartwise conclusion in the item.

I checked B1-B10: the two unsplit inputs have no proof or proof dependencies, introduce every object, define sheaf-surjectivity explicitly, cite the actual notion nodes, use single-escaped TeX, have exact source tags and labels, carry blueprint provenance and actual logged search results, and have no fabricated Lean attachment or Mathlib leaf. I checked C1-C8 by opening each cited statement and comparing it to what the step takes; citations.json copies those statements without paraphrase. In particular I added the fibre-product existence citation rather than silently assuming the sheaf products were algebraic spaces. The two off-unit uses declared in split_report.tool_uses are only generic fibre products and scheme coproducts; neither replaces the unit route. I did not set maintainer-owned tool_uses.

For D1-D5, the new inputs expose genuine prior lemmas, not item clauses, and the five steps supply the intervening argument. For E1-E7, the types of all three factors, the two restricted projections, and the base-change targets were checked explicitly. Tested empty base, trivial group, a finite constant group, nonsmooth alpha_p over a characteristic-p field, and the identity-map cases of 06NR and 06PJ. Alpha_p confirms that smoothness of G must not enter; the empty-source case of 06NR forces an empty Y under the sheaf-surjection hypothesis. For a trivial group the quotient is B and the conclusion is the identity map. No new hypothesis is needed. I checked the combined statement/proof dependency closure and found no path back to the item. Every proof step is shorter than 2000 characters, and the longer assembly step was checked for hidden comparison claims as described above.

## Unfinished work

None for this one-level split. The two new statement-only inputs remain unsplit as required; their arguments will be separate stage-1 items. Required server dry run and direct push follow this report.
