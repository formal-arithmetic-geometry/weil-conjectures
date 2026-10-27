# Worker report — Q102

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-derived-coherator-bound.json: item, six-step split; original statement retained; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-coherator-formula.json: statement-only lemma, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-coherator-distinguished-square-triangle.json: statement-only lemma, unsplit; no Mathlib match.
- citations.json: exact statement excerpts for every proof-step citation.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id and coherator/DQ terminology. Existing DQCoheratorAdjunction and DQCoheratorDerivedGlobalSections declarations are about schemes and adjunction/global-section detection, not the algebraic-space uniform bound. No Lean was written or compiled.

## WANTED

None. All sources used are present in literature/stacks-project.

## Corrections and unfinished work

The item was unsplit and the sandbox had no earlier item, report or search log. Its statement is faithful to Tag 0CSS and was not changed. The source proof has harmless notation slips: X in the W-square paragraph, RQ where DQ is intended, and U cap V where the fibre product U times_W V is intended. The split consistently uses W, DQ and that fibre product. The source's concluding enlargement of N is made explicit: the overlap term contributes one further degree through H^(i-1)(B_T). No mathematical hypothesis is added.

The two new nodes remain statement-only, as required for a one-level split. Their future proof routes are already in the sources: the affine formula follows 08H0 and uniqueness of the right adjoint; the triangle is 0CR6, applying the exact coherator to 08GW and using 0CR5. Those routes are recorded here, not as proofs inside the unsplit nodes. Nothing in the assigned split remains unfinished.

The inherited blueprint.from.node is null and the ancestor command returns None, because this supporting chain has no imported ancestor under the tool's current records. I preserve that provenance and its via list, and provide a precise from.place for each helper. The latest blueprint's direct-image proof paragraph (3) is the inherited unit provenance; the Stacks coherent-effectivity helper is not itself a blueprint duplicate or a replacement proof for constructible direct-image stability. This is not the unit key node; no realized fields were edited.

## Searches and existing material

Searched the whole DAG by coherator, affine hypercohomology, distinguished-square induction, source labels and Tags 08H0/0CR4/0CR5/0CR6/08GW. Ran blueprint_refs ancestor and blueprint searches for coherator, affine coherator, coherator distinguished, derived global sections and distinguished square. No imported blueprint node states either helper. Reused the existing space affine realization, induction, qcqs permanence, chart calculus and pushforward bound rather than duplicating them.

For the item and each new node ran two different LeanFinder phrasings, Loogle, Mathlib grep and LeanSearch with the required msearch.py command. Full actual outputs are retained in search-results.json, with the command's audit in searches.jsonl; the node records contain exactly these queries and outputs. All services answered. Hits included DerivedCategory.IsGE/IsLE and representatives, ModuleCat.tilde and ordinary scheme global sections, SheafOfModules.IsQuasicoherent, and GrothendieckTopology.MayerVietorisSquare. I read the latter's structure and its sheaf-cohomology sequence: it is an abelian-sheaf sequence on a given site square, without a derived quasi-coherator or its commutation with pushforward. It cannot specialize in one line to the new triangle. Underived quasi-coherence and tilde likewise do not identify a right adjoint on arbitrary ambient unbounded complexes.

## Not duplicates

lem-sfb-space-affine-coherator-formula vs lem-sfb-space-derived-coherator-adjunction: shared Tag 0CR4 only identifies which right adjoint is being computed; the existing node asserts existence, exactness and its adjunction, but gives no affine computation by RΓ.
lem-sfb-space-affine-coherator-formula vs lem-sfb-affine-etale-derived-module-realization: existing equivalence has quasi-coherent input; the new formula computes DQ on every ambient complex, which need not be quasi-coherent or bounded.
lem-sfb-space-affine-coherator-formula vs lem-sfb-affine-derived-coherator: existing node is for the Zariski scheme coherator and its unit/counit, not the small-etale ambient formula.
lem-sfb-space-coherator-distinguished-square-triangle vs lem-sfb-space-derived-hom-mayer-vietoris: existing statement is a long exact sequence of Ext groups; it supplies neither the derived-object triangle with DQ nor coherator/pushforward interchange.
lem-sfb-space-coherator-distinguished-square-triangle vs lem-pc-derived-mayer-vietoris-triangle: existing node is for a union of scheme opens, not an elementary distinguished square of spaces or a coherator triangle.

## Review by Q102

I read Tag 0CSS (spaces-perfect.tex, lemma-boundedness-better-coherator) in full, its affine reference 08H0 (lemma-affine-coherator), and the statements and proofs of 0CR5 (lemma-pushforward-better-coherator), 0CR6 (remark-explain-consequence), and 08GW (lemma-exact-sequence-j-star). I checked 08GP's induction hypotheses and 08FA's upper bound, and read sites-cohomology.tex 08FI and 0D6F for restriction of unbounded K-injectives and derived evaluation. These are all small-etale structure-sheaf module statements; no constant-coefficient or Zariski comparison has been silently substituted, and no SGA source is used.

Step 1 cites the full existing induction statement, which explicitly permits etale algebraic-space objects and all three smaller vertices, and the coherator adjunction, which applies to every qcqs vertex. The invariant P quantifies over all windows and complexes with a single constant per space; this is the right induction predicate. Step 2 uses the new derived-category isomorphism, not a degreewise replacement for it, followed by the existing affine realization's explicitly stated cohomology comparison. The affine identity is indeed among the test maps, so N=0 works.

In step 3 I checked the chart-calculus statement really says etale pullback is exact slice restriction. The sheaf-slice adjunction really supplies an exact left adjoint for module restriction and permits slices by arbitrary sheaves, so it also covers algebraic-space vertices that are not scheme objects of the small site. The K-injective definition and that adjunction give the written two-line null-homotopy argument; no extra comparison lemma is hidden. Sectionwise equality under relocalization then identifies the two evaluation complexes. This step is elementary from those cited statements and its actual argument is included.

Step 4 uses only the previously established inductive bounds on Q_A, whose cohomology is quasi-coherent because DQ lands there. I read the permanence statement: qc source and qs target make each j_A qc, and qs source makes it qs. W is qc, exactly the extra hypothesis in the existing upper-bound node. Its bound is i >= b+N_A+c_A, so the inclusive upper endpoint is b+N_A+c_A-1. Chart calculus gives the derived adjunction to exact restriction; clause (1) of the generic exact-derived-adjunction node supplies the lower bound a. I use none of its other clauses. The two off-unit generic tools are declared in split_report.tool_uses with their purposes.

Step 5 takes exactly the new triangle's three pushforward terms, and the existing derived-homology long exact sequence supplies its segment H^(i-1)(B_T) -> H^i(DQ_WE) -> H^i(B_U) plus H^i(B_V). Checking this segment shows the lower bound is a (not a-1), and the upper endpoint can be b+M+1. Step 6 merely applies the same induction statement after its two conditions have been established. Every cited node's statement was opened, and citations.json was checked for literal substring agreement. No citation takes a construction from an existing node's proof instead of its statement.

I tested E=0, the empty affine scheme, a=b, negative a and b, and a square with empty overlap. The constants are all nonnegative, independent of E and the window, and the argument does not assume E has quasi-coherent cohomology. Both new nodes introduce their own objects, derived functors, sites and hypotheses and have no proof/proof_deps. They are not clauses of the uniform bound: one computes an affine functor, the other gives a general descent triangle with no bound hypothesis. No step exceeds 2000 characters. I checked delivery-errors B through E against the actual files and sources, including duplicates, exact statement citations, the potential overlap shift, and the absence of extra finiteness or dimension hypotheses. The server review_split check passed before this report was written.
