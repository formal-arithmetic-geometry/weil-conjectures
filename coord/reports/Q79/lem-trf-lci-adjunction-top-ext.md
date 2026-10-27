# Stage-1 report: lem-trf-lci-adjunction-top-ext

## Files written

- dag/nodes/sec-trace-formula/lem-trf-lci-adjunction-top-ext.json: statement split into three proof steps; no Mathlib match.
- citations.json: one verbatim statement excerpt for each citation in each proof step.
- report.md: this report.

New nodes: 0. Mathlib leaves: 0. The existing statement, source, ancestry, created record and historical searches are retained. Added only definition dependencies for the tensor product and the derived cohomology notation actually used. The proof has 2191 characters altogether, with every individual step below 2000 characters.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, lci adjunction, normalized Koszul comparisons, conormal determinants and top Ext found no declaration stating the whole item. AlgebraicGeometry.koszulRegularImmersion_ext_constantRank_top in lean/WeilConjectures/AlgebraicGeometry/KoszulExtConstantRankTop.lean:55 concerns scalar coefficients O_Y, then pullback and restriction to a rank stratum. It does not give the ambient top-differential coefficient or the named normalized inverse required here. It belongs to the already existing lem-sc-koszul-ext-constant-rank-top, not this item.

## WANTED

None. The source needed here is present locally.

## Corrections and findings

The imported item had no proof. Its statement is correct and unchanged. The precise source is Stacks duality.tex, Tag 0BQZ, lemma-regular-immersion-ext. I read its local dual-Koszul calculation including the last warning about signs. The signed coefficient comparison and its independence statements are already available as the statement of lem-trf-lci-koszul-duality-determinant-comparison, which the item's statement explicitly names. Reproving that comparison or creating a new node for one of its clauses would duplicate existing work. No purity theorem or SGA source is used.

The chapter and unit records were read. This is an auxiliary descendant, not the key node of sk-i-curve-zero, so no unit realization fields are changed. The current main-20261015 blueprint's lem-trf-local-term-locality proof was read; it has no separate adjunction lemma. The inherited exact ancestry place records the downstream marked-dualizing input and its explicit re-split request for the degree-c consequence. No unit route is replaced. The only statement theorem used is the existing comparison in the same unit; all further citations define the constructions.

## Searches and duplicate check

Searched the entire DAG for Tag 0BQZ and the relevant Koszul, adjunction and conormal terms, and ran tools/blueprint_refs.py ancestor and searches for Koszul, adjunction, regular immersion and conormal determinant. Existing scalar derived-Hom and top scalar Ext nodes were read. They do not state this normalized ambient-line version, and the existing normalized derived comparison is reused directly. No new node is created, so there are no new-node/existing-node duplicate pairs.

All five fresh Mathlib queries were run through msearch.py with Q79 and this item, with results recorded verbatim from searches.jsonl in the node. The two LeanFinder phrasings return global Ext computations, cotangent exactness and open-restriction functors. LeanSearch likewise returns sheaf cohomology and closed/open immersion tools. Loogle's two hits CommRingCat.KaehlerDifferential.ext and ext_iff are extensionality statements, as reading Basic.lean:119 confirms. The grep hits are algebraic cotangent exactness or similarly named extensionality, not normalized sheaf Ext. The original historical searches are preserved separately; none is represented as a new search performed by Q79. All fresh services answered successfully.

## Unfinished work

None in this one-level stage-1 split. The existing comparison node remains responsible for its own derived construction; this item only takes its cohomology as expressly intended by its statement.

## Review by Q79

I checked delivery-errors sections B through E against the actual statement and source. There are no new nodes to conceal a missing proof, no new lemma restating an item clause, and no new unsplit node with a proof hidden inside its statement. The mathematical work here is a formal consequence of an existing stronger derived assertion and the definitions, written out rather than renamed.

For step 1 I opened the full statement of lem-trf-lci-koszul-duality-determinant-comparison. Its unconditional first assertion gives exactly the required rho_i, over O_P and with the quotient action, independently of any later relative-duality existence hypothesis. Set X=U and use the one-element cover U. The integer d=n-c is nonnegative, c=n-d, and all immersion, polynomial-chart, Koszul regularity and conormal-rank hypotheses are present. Thus there is no hidden flatness, separatedness or Noetherian requirement. The citation quotes the actual displayed rho_i formula.

For step 2 I read def-weil-pbc-sheaf-ext, def-weil-abstract-derived-category and def-weil-derived-cohomology-sheaves. Their statements respectively define Ext as H^c RHom, define the shift with (K[1])^r=K^(r+1), and identify cohomology as kernel modulo image. Hence shifting a degree-zero sheaf by [-c] places it in degree c. The explicit zero-kernel/image computation gives i_*D_i, and functoriality takes inverse maps to inverse maps. No derived projection formula, exactness of closed pushforward, or exterior-power base change is needed: the target of the existing derived comparison is already precisely i_*D_i[-c]. This is a short elementary computation from the cited definitions.

For step 3 I reread the comparison statement's independence and open-restriction sentence, and the cohomology definition. Equal derived maps stay equal under H^c; their inverses stay equal by the inverse identities. Restriction to an open does not change local kernels, images or quotients in the cohomology formula, which explains explicitly why the compatibility passes to H^c and to its inverse. This step uses no unmentioned comparison theorem. Every citation has its verbatim excerpt in citations.json, checked by substring against the current node statement.

The edge cases checked were c=0 (the empty Koszul sequence, no shift), n=c (d=0, allowed by the comparison's unconditional assertion), n=c=0, and empty U or P (zero sheaves and the unique isomorphism). The degree sign gives H^c(M[-c])=M in each case; no inverse shift or extra sign is inserted. The Stacks proof's normalization warning is respected by using the existing rho_i rather than choosing a new top generator map. Each proof step is below 2000 characters and contains no independent non-elementary sublemma needing extraction.
