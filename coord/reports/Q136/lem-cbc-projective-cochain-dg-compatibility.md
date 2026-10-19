# Stage-1 report: lem-cbc-projective-cochain-dg-compatibility

## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-projective-cochain-dg-compatibility.json: statement, split; no Mathlib match. Nine explicit proof steps, no new nodes and no Mathlib leaves.
- citations.json: verbatim excerpts of every node cited in every proof step.
- report.md: this report. The interrupted attempt's split, citations and searches.jsonl were retained; its write_split.py is scratch work and is not delivered.

## Attachments

None. Searched WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the exact blueprint id and for differential graded/projective model terminology, and checked dag/lean_names_upstream.json. The hits on geometric projective models do not state this assertion. No project declaration covers the item.

## Wanted literature

WANTED: Choudhury--Gallauer Alves de Souza, arXiv:1511.02828v1, Example 2.7(2), Fact 2.8 and section 3 opening, for lem-cbc-projective-cochain-dg-compatibility. The inherited source mentions this unarchived reference. The delivered proof does not assume its assertions: it is explicitly agent-written, using the local Stacks sign conventions and existing DAG model-structure statement.

## Audit and corrections

The imported item was statement-only. Its statement and statement dependencies are unchanged. The model compatibility over abelian-group complexes needs a mixed-coefficient verification; closed monoidality over R alone should not be silently identified with it. The split constructs the mixed tensor and cotensor and gives both signed complex adjunctions, then proves the Hom comparison by lifting from projective R-modules. In particular it assumes no projectivity of R over Z.

The chapter sec-smooth-purity and unit sk-prop-sf-cbc were read, together with the current main-20261015 thm-cbc-finite-level-proetale proof and the existing cosimplicial-complex-holim statement. This item supplies the extracted algebraic descent foundation and does not change the compactification/site-comparison route. It is not the key node of its unit, so no realized fields were edited. The inherited chapter, unit and blueprint ancestry are retained. A whole-blueprint search for differential graded gave no equivalent blueprint statement; the whole-DAG concept search found the existing model and enriched-calculus inputs, not a duplicate of this mixed-coefficient compatibility assertion.

The five recorded searches in searches.jsonl were read and reused without rerunning them: the HomologicalComplex quasi-isomorphism and retract results do not give enrichment or the Hom comparison; CochainComplex.IsKProjective and its transport/shift results concern K-projectivity. Read Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean, lines 35–51: the condition is null homotopy into acyclic complexes, with its Hom-complex reformulation still a TODO. Read Mathlib/Algebra/Homology/ModelCategory/Injective.lean, lines 45–56: that structure is bounded-below injective and is not this unbounded projective assertion. Thus neither the full item nor a one-line specialization is furnished by the hits. The saved searches are appended to the item's inherited search history, preserving the actual queries and returned names. No new node needs duplicate-tag comparisons.

Two generic off-unit tools are declared in split_report.tool_uses: lem-coef-projective-cochain-monoidal-model supplies the algebraic model and dg-projective cokernel condition; lem-coef-quillen-section-rectification supplies only the opening definition of the requested compatibility axiom. They replace no geometric step of this unit. The cochain conventions and projectivity definition are definition inputs; the long exact sequence node is an existing Mathlib leaf.

## Unfinished work

None at this stage. No Lean files were written or compiled. The dependencies remain independent DAG tasks; they were not split here. The initial resumed server review_split check passed.

## Review by Q136

I read delivery-errors.md B–E in full and checked its failure cases against the saved split. There are no new nodes, so statement-only children, new duplicate tags and new statement counterexamples do not arise. For the item I read Stacks more-algebra.tex, section-hom-complexes (0A8H), lemma-compose (0A5Y), lemma-composition (0A8I), and section-symmetric-monoidal (0GWN); homology.tex, lemma-long-exact-sequence-cochain (0117); and algebra.tex, lemma-characterize-projective (05CF) and the preceding lifting characterization. The proof is marked agent-written because the mixed-coefficient and model comparison arguments are supplied explicitly, not quoted from a missing source. No SGA source is used.

For step 1 I opened lem-coef-projective-cochain-monoidal-model and def-weil-abstract-derived-category: they provide the unbounded category, model and cochain convention actually invoked. The product-total differential and the Leibniz identity are expanded directly, giving enrichment without a boundedness assertion. Steps 2 and 3 use no external lemma: tensor and product-Hom terms, induced R-actions, differential squares, universal-property currying, and the two differential formulas are written down. I checked the second curry sign (-1)^(pq): its d_T and d_A terms have exactly the signs displayed. The associator and unit act on pure tensors, with the same three differential signs on either association. Step 4 uses only quotient/kernel universal properties and checks compatibility with the differential; the kernel identification therefore does not assume a chain splitting.

For step 5 the model node expressly states that a cofibration is a termwise split injection with dg-projective cokernel, that this cokernel has projective terms, and that fibrations are termwise surjections. The cited def-weil-pbc-projective-module expressly gives lifting along surjections. These are exactly the hypotheses needed to lift v s separately in each degree. I checked w=ur+ell q against both required equalities; no lift is wrongly required to be a cochain map.

For steps 6 and 7 I opened lem-weil-pbc-complex-ses-homology-long-exact: it covers Z-indexed complexes in any abelian category and degreewise short exact sequences. The sequences with kernel K and cokernel P meet that hypothesis by the fibration and cofibration descriptions. Its exactness gives respectively the acyclicity of K and P. The model node's statement explicitly gives acyclicity of Hom(P,N) for every acyclic N. In step 7 this is applied to N=P; the identity is a boundary, giving dh+hd=1, and I checked delta((-1)^n f h)+(-1)^(n+1)(delta f)h=f. This proves the arbitrary-K case directly rather than citing an unstated contractibility theorem. Step 8 applies the same long exact sequence in abelian groups to the degreewise short exact comparison sequence, obtaining all cohomology isomorphisms.

For step 9 I reread the opening paragraph of lem-coef-quillen-section-rectification: its Hom compatibility is precisely degreewise surjectivity, trivial in the two specified cases, in the abelian-group projective model. The model node applies to R=Z and supplies that description and combinatoriality. No section-rectification theorem is being used. Every use in these nine steps has a verbatim statement excerpt in citations.json; I verified each excerpt against the current repository copy. proof_deps is exactly the union of uses.

I tested the boundary cases R=0, zero complexes, i an identity and p an identity: the comparison and zero kernel have the asserted behavior. For R=Z/mZ the lifting is over R, so the absence of underlying Z-projectivity creates no extra hypothesis. The Hom formulas use products over all integers and the tensor uses direct sums, hence the proof never changes the unbounded statement to a bounded one. Every proof step has fewer than 1100 characters; none hides a long comparison lemma. There is no statement dispute or route change, no circular new node and no clause moved into a new node.
