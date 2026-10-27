# Stage-1 report: lem-sfb-ordered-join-prefix-telescope

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ordered-join-prefix-telescope.json: item, statement; split into five elementary algebraic steps, not a Mathlib leaf.
- citations.json: the verbatim definition quotation used by step 1.
- searches.jsonl: real search results appended by msearch.py; the item's existing recorded searches were preserved.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean written or compiled. The original statement and its statement dependency are unchanged.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint id, ordered homotopy, prefix telescope, proper color and boundary commutation found no declaration stating all clauses. Ordered Cech projection homotopy declarations concern different complexes and hypotheses.

## WANTED

None. The item explicitly identifies itself as an agent generalization, not a theorem quoted from the blueprint. The elementary argument is written here and in the item, marked proof_origin.by = agent.

## What was wrong and what changed

The live item was statement-only. The sandbox had no prior node, report or search log, only dispatcher brief markers. There was no released repair note. The statement is correct: no STATEMENT-DISPUTED correction was needed. I preserved its source/history fields and added proof steps and a source pointing to literature/blueprint/latest/. Its existing blueprint ancestor is null; blueprint_refs.py ancestor confirms this. The recorded via chain is preserved, its place is already explicit, and same_as is empty after searches.

The current direct-images proof paragraph (3) establishes the context of open and proper direct images; it does not assert this homological calculation. I read that paragraph, the current unit's _section.md and main proof, the chapter record and the unit record. This split only supplies the existing auxiliary algebraic step below that route. It changes neither the unit nor any coefficient category. There is no SGA citation.

## Mathlib and duplicate review

Read the item’s seven inherited searches and their results. New searches used leanfinder twice with different descriptions, loogle, leansearch, and three grep patterns; exact queries and returned records are in searches.jsonl and mathlib_searches. LeanSearch was available in this run. The first grep hit Data/List/Chain.lean concerns relation chains. The other hits include Homotopy.comm, Homotopy.comp, the inductive constructors, and DoldKan.homotopyPToId and homotopyPInftyToId. Read Homotopy.lean:130–235 and HomotopyEquivalence.lean:25–82. Homotopy.comp assumes existing chain maps and constructs composites of two homotopies; it does not state the whole ordered-prefix expression and subgroup-annihilation clause. Dold–Kan's P is a particular simplicial projection, not arbitrary degreewise R_i. Thus the item is not an exact match or a one-line specialization, although Mathlib tools can implement parts of its elementary proof.

Whole-DAG keyword searches and blueprint_refs.py searches for telescop, prefix and ordered found no imported statement equal to this item. Read the statements of ordered-join-partial-contraction, equivariant-prefix-finite-chain-homotopy, homogeneous-tuple-prefix-homotopy, closed-cover-retractions-stabilizing-selectors and norm-algcl-ordered-finite-model-filtration. The parent uses this abstract calculation for ordered joins; it is not an independent lemma to cite backwards. The other prefix lemmas concern explicit tuples, not arbitrary groups and proper-support subgroups. No new node was created, so there are no new/existing tag pairs requiring a Not duplicates section. No elementary step or clause of the item was relabelled as a new node.

## Review by Q106

I checked the statement against its stated agent origin and the current blueprint context described above. The only cited node in the proof is def-weil-pbc-module-chain-complex-homology in step 1. I opened its full statement, which explicitly defines integer-indexed differentials d_n with d_(n-1) composed with d_n equal to zero, and chain-map boundary commutation. I also read Stacks homology.tex, section-complexes (Tag 010V), at the chain convention paragraphs. The quotation in citations.json is copied verbatim from this node, not from its proof. I do not use its homology or induced-map clauses.

Step 1 expands R in degrees q and q-1, and separately cancels d_q d_(q+1) and d_(q-1) d_q. Every map's source and target agree, including the c_(i,q-2) term. Square-zero is an explicit hypothesis, so no theorem asserting a homotopy induces a chain map is being silently invoked. Step 2 states an induction simultaneously in q: the base is the identity prefix, and the successor uses precisely step 1 and the prefix recursion, with no interchange of factors. Steps 3 and 4 distribute finite sums and compositions of homomorphisms and cancel consecutive prefix differences; the telescoping induction includes the empty sum. These use only additive-group laws and the preceding calculations, no additional node.

Step 5 uses the support hypotheses only in the fixed degree where they were assumed. For x in A_(q,C), choose a missing j. The factors with indices greater than j act first and each preserves this same subgroup; R_j kills their output; the remaining factors preserve zero. Finally the explicitly assumed finite-sum generation and additivity extend zero to the whole group. There is no assumption of commuting R_i, a direct-sum decomposition, unique representations, or support preservation across degrees. This is a few-line elementwise calculation, not a hidden comparison theorem.

I tested r=1: P_1=R_0 and H=c_0, and the only proper support is empty, so the extra hypotheses force R_0=0. At r=2, H=c_0+R_0 c_1 and the boundary sum is (1-R_0)+(R_0-R_0 R_1). On the two-term contractible complex A_1=A_0=Z^2 with d_1=id, arbitrary matrices R_0,R_1 are realized by c_(i,0)=id-R_i. Thus the formula applies even to noncommuting matrices: H_0=(id-R_0)+R_0(id-R_1)=id-R_0 R_1, confirming the order. For C empty every R_i kills its subgroup; missing j=0 and j=r-1 verify the empty-prefix and empty-suffix cases. Zero groups cause no exception. Allowing a full support C=I would invalidate annihilation (all R_i=id), which confirms the necessity of properness. No direct-sum uniqueness is needed because zero is proved on every summand of every permitted finite representation.

I reviewed B–E point by point: all objects and hypotheses were already self-contained, every non-elementary external fact would require a node but none occurs here, no citation claims more than its statement, no new duplicates or restatements were introduced, and the written induction and factor order close the possible gaps. Each step is under 2000 characters. All proof steps are explicitly elementary and together have 2178 characters.

## Unfinished work

None at stage 1. The independent maintainer review remains the acceptance step.
