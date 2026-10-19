# Worker report

Group Q22; item lem-trf-generic-fibre-closed-chain; stage 1; 2026-10-18.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-generic-fibre-closed-chain.json: statement node, split into five steps; no exact Mathlib match. Its mathematical statement is preserved; generic-point, stalk and residue-field references are now explicit, with the missing residue-field definition added to stmt_deps.
- citations.json: one verbatim statement quotation for each of the 15 step/node citations.
- searches.jsonl: seven actual msearch queries, their service results and digests. Existing Q48 search records in the item were retained; the additional Q22 records are copied from this log, not reconstructed queries.
- report.md: this report and self-review.

New nodes: 0. New Mathlib leaves: 0. No Lean files, unit records, chapter records or shared files were changed. No compiler, Lake or build command was run.

## Attachments

None. I searched the read-only WeilConjectures source by the full blueprint tag and by generic-fibre, closed-point, chain, dimension and transcendence-degree notions. There is no project declaration stating all the item's clauses with the item's hypotheses. The existing Mathlib/source function-field and closed-point declarations are ingredients only. Master source was not used as evidence of completed proofs.

## WANTED

None. The Stacks sources and the relevant blueprint texts are available locally.

## Problems found and changes

The item had no proof. It already required distinct points and a chain beginning at the generic point, beyond the unexpanded maximal-local-chain sentence in the source. Step 5 proves those endpoints explicitly by ruling out a chain longer than dim A. I did not weaken that statement or assume X quasi-compact, separated, proper, normal, or smooth.

The original stmt_deps omitted the residue-field definition although the statement used kappa(x). I added it and made the existing generic-point/stalk references explicit. These are notation clarifications, not a mathematical statement correction. There is no STATEMENT-DISPUTED or source error.

The sibling lem-trf-local-dimension-formula gives only an inequality. It cannot justify the equality needed here, and the parent lem-trf-closed-dominant-dimension depends on this item. I therefore use the already-existing generic field-algebra equality lem-weil-pbc-finite-type-domain-dimension-trdeg, including its maximal-local-ring clause. This realizes the same field-base dimension computation that 02JX invokes via the dimension formula, without a circular appeal to the parent.

## Blueprint and duplicate searches

I read dag/chapters/sec-trace-formula.json, dag/units/sk-i-curve-zero.json, and the current main-20261015 lem-trf-local-term-locality proof. The item's existing ancestry points to the normal-cone/alteration branch under that unit. This is an auxiliary dimension argument under that branch, not a change to the trace, pairing, or purity route. The unit key node is lem-trf-local-term-locality, so this worker does not change its realized fields.

The ancestor command identifies lem-trf-local-term-locality. Blueprint searches for "generic fibre closed point dimension chain", "dimension formula", and "closed point", together with DAG/blueprint keyword searches and searches for 02JX, 00P0, Jacobson, finite residue fields and chains, found no blueprint node with this full statement. same_as is therefore empty. Existing nodes supply every ingredient. In particular, the finite-type-domain dimension node was reused instead of creating another 00P0 statement; the Jacobson and fraction-field facts are existing Mathlib leaves. No new-node duplicate pairs arise.

## Tool uses

The split_report declares three generic black boxes from other units: lem-kun-closed-point-field(a), the two clauses of lem-weil-pbc-finite-type-domain-dimension-trdeg, and part (1) of lem-weil-pbc-localization-prime-residue-field-iso. They supply Nullstellensatz, the field-base dimension theorem, and the localization prime correspondence, respectively. No node of the trace-formula unit provides these generic algebraic statements. Definitions and the existing Mathlib leaves are not replacements of the unit route. I checked that none of the three dependency closures reaches the item.

## Review by Q22

I read Stacks morphisms.tex Tag 02JX, label lemma-alteration-dimension, including the entire equality proof. Its generic-fibre argument chooses a Jacobson closed point with finite residue extension, computes local dimension r, and takes a chain of that length. I also read varieties.tex Tag 0478, label lemma-locally-finite-type-Jacobson, its statement and proof; algebra.tex Tag 00P0, label lemma-dimension-prime-polynomial-ring, both dimension clauses and its proof; and algebra.tex Tag 00E3, label lemma-spec-localization, its statement and proof. I checked these tags against tags/tags. For the finite-residue-field clause I read the existing lem-kun-closed-point-field statement and its source blueprint file, which states exactly the needed implication for finite-type schemes. No new-node sources are needed. Every step has a document and source place, and no SGA source is used.

For step 1 I opened lem-sc-lft-over-field-jacobson-space: its statement says the ambient closed points in every closed subset are dense, not merely that some affine chart is Jacobson. Taking the subset X gives a closed point because X is nonempty. This uses the actual locally-finite-type hypothesis and requires no global finite-type assumption.

For step 2 I opened def-weil-finite-type-morphism and def-pc-integral-scheme. The former supplies an affine cover by finitely generated K-algebras; the latter makes the nonempty chart ring a domain. I checked that the chosen chart contains x, that closedness restricts to its open subspace, and that the single affine chart is itself finite type. Thus the finite-type hypothesis of lem-kun-closed-point-field(a) really holds on U, even though it need not hold on X. The germ description of def-weil-pbc-module-stalk and quotient description of def-weil-residue-field give the written cofinal-neighbourhood identification of the two residue fields. No affine stalk-identification theorem is being used without citation.

For step 3 I opened lem-sc-integral-function-field-affine-fraction. It explicitly says eta is in U, A is a domain, and the germ map makes the generic stalk a fraction field; it is not just a definition of the function field. Constant-section germs make this a K-field identification. I opened lem-weil-pbc-finite-type-domain-dimension-trdeg and checked that it states both dim A = trdeg Frac A and equality with the local dimension at every maximal ideal. The field, finite generation, domain and maximality hypotheses have all been established. Its finiteness clause makes r an actual finite integer, so the later supremum and length arguments are valid.

For step 4 I opened def-weil-pbc-krull-dimension-ring and def-weil-pbc-localization-at-prime, then the full statement of lem-weil-pbc-localization-prime-residue-field-iso. I use only its prime bijection with inverse extension, not its proof or a nonexistent chain clause. The fraction formula checks all three localization hypotheses explicitly. Contraction preserves inclusion and the inverse proves strictness. Disjointness from A minus m means every contracted prime is contained in m. The maximum of the finite set of possible integer lengths is explained, including r=0 using the local maximal ideal.

Step 5 is elementary: prepending the zero prime or appending m would contradict dim A=r. I checked the direction of the specializations: p contained in q means q belongs to V(p), hence p specializes to q. The generic point corresponds to the zero prime because its closure contains every prime of the domain. The open-subspace inclusion preserves closure relations and distinctness. Thus the produced chain has exactly r strict steps from eta to x; it is not just an unanchored chain of length r. No independent sublemma is hidden in this short endpoint argument.

I checked B1--B10: there are no new nodes, the item is self-contained, the added definition says exactly what it is used for, TeX is encoded once, source tags/labels agree, blueprint references are filled, and the Mathlib/source checks do not justify an attachment. The seven Q22 searches are actually logged; the first Loogle query rejected the unqualified name trdeg, so I also ran the valid quoted-name query, which returned zero hits. Semantic searches with two phrasings and the grep results found only ingredients, which I read in their returned signatures. I retained the inherited search records separately from these actual Q22 searches.

I checked C1--C8 by reading every cited statement and producing citations.json: all substantive inputs have a node, no cited inequality was treated as an equality, no node's proof was used in place of its statement, and generic off-unit tools are declared. I checked D1--D5: the item's steps carry the choice, finite-type reduction, chain existence and endpoints; no clause is merely moved into a new node and no induction or proof is assumed. All five steps are under 2000 characters. I checked E1--E7 by tracking the affine chart, the exact fraction field, the residue field, and the specialization direction; no source error or missing hypothesis was found.

Small cases: X=Spec E for a finite extension E/K has r=0 and the chain is its sole point; affine space K[t_1,...,t_r] has the familiar strict prime chain ending at a closed point; a closed point with nontrivial finite residue extension is allowed over a non-algebraically-closed K. The affine line with doubled origin and schemes with infinitely many charts require neither separatedness nor quasi-compactness in this argument: the Jacobson point and its finite-type chart suffice. The empty scheme is excluded by the statement. Both chain endpoints and the finite residue extension survive these tests.

## Unfinished work

None in the mathematical split. The required remote checks and direct delivery follow this report; their results are recorded by the delivery tool.

Remote check: review_split PASS (0 new nodes). The first delivery dry run requested at least 40 characters for the closed-point-field quote; I expanded it to the complete clause (a), preserving the exact statement text. No mathematical change was needed.
