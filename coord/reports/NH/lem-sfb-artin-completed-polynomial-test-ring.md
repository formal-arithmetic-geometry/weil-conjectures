## Worker report

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-artin-completed-polynomial-test-ring.json (statement, split; no whole-item Mathlib match), citations.json, and this report. No new nodes and no new Mathlib leaves. searches.jsonl records the four required current searches; write_split.py is a sandbox-only preparation script, not a delivery file.

Attachments: none. Searched lean/WeilConjectures for the item tag, completed-polynomial terminology and relevant polynomial-completion declarations. PolynomialLocalCompletionFormallySmooth states adic formal smoothness for a localized one-variable polynomial algebra, not this whole assertion; it is not an attachment. No Lean was written or compiled.

WANTED: none.

The item had no proof. Its statement is mathematically correct. Two notion citations were inaccurate: finite type of a ring algebra cited the scheme-morphism node, and a multivariable polynomial ring cited only a univariate definition without its evaluation property. Replaced these with def-weil-pbc-finite-type-algebra and def-weil-pbc-mv-polynomial-ring, respectively; hypotheses and conclusions are unchanged. The blueprint ancestry inherited from the Q15 node has from.node=null: tools/blueprint_refs.py ancestor likewise returns None. Preserved its precise from.place and historical via chain. The latest blueprint direct-images proof (3) was read: it now assembles proper and open direct images. The present item is the already imported supporting algebra lemma on the recorded alteration/Artin route, not a proposed change to the unit.

Nothing mathematical remains unfinished. The split uses the existing general algebra theorems rather than creating duplicates. Required server checks and push are recorded by the delivery tool.

## Searches and reuse

Read the item's original Mathlib searches and their hits. Ran a second whole-item natural-language search with LeanFinder and LeanSearch, plus Loogle AdicCompletion, IsNoetherianRing and the recorded completion/Noetherian grep pattern through msearch.py. The hits include completion projections, locality and algebra lifting constructions, but none states all the item's clauses or specializes to all of them in one line. Reused the original searches as provenance and appended current searches faithfully from their logged results. LeanFinder and LeanSearch both returned results, so neither is marked unavailable.

Searched the whole DAG for completion Noetherianity, quotient projections, Artinian local nilpotence, Artinian quotients, and Noetherian polynomial algebras. Read the actual statements of all selected dependencies. tools/blueprint_refs.py searches for completion, Artinian, polynomial Noetherian, Hilbert basis, and completion Noetherian found no blueprint statement of the whole item. Existing created nodes supply all needed algebra tools. In particular, the general finite-type Noetherianity node avoids duplicating the integer-only lem-trf-mvpolynomial-noetherian. No new node was created, so no same-tag duplicate pair needs justification.

## Review by NH

I read formal-defos.tex, Tag 06SM (lemma-exists-smooth), including its construction of a completed smooth algebra and its final lifting argument. The minimal cotangent assertion is deliberately outside this item's statement; the proof here uses polynomial evaluation directly, so does not assume separability or minimality. I read algebra.tex at Tag 00FN (lemma-Noetherian-permanence), Tag 05GG (lemma-hathat-finitely-generated), Tag 0316 (lemma-completion-Noetherian-Noetherian), Tag 00J8 (lemma-artinian-radical-nilpotent), and Tag 00KH (lemma-Noetherian-dimension-0). All are available sources; there are no new nodes needing further sources.

Step 1 uses the actual general finite-type algebra theorem: the finite list of variables generates P over the given Noetherian R. The definition of Noetherianity then gives finite generation of q. Surjectivity to the nonzero field k proves maximality without assuming P local.

Step 2 takes exactly Noetherianity from lem-weil-pbc-adic-completion-noetherian. It takes completeness, surjectivity and the precise projection kernels from lem-weil-pbc-module-completion-complete with A=M=P and I=q; finite generation was established in step 1. Its module statement suffices: the maps themselves are ring projections, and equality (qS)^n=q^nS identifies their kernels with the required ideal powers. I did not take locality or residue fields from the Noetherianity theorem, since it asserts neither.

Step 3 proves locality rather than quoting a hidden completion-locality lemma. Its compatible finite geometric sums give an inverse to 1-t in the complete ring; separatedness verifies the product equality. Every element outside J is consequently a unit and every element of J is a nonunit. This also identifies the actual residue map and does not require R or P to be local.

Step 4 applies the full statement of lem-weil-pbc-noetherian-local-quotient-artinian-local. Noetherianity and locality have already been proved. Its hypotheses are precisely J^n contained in L contained in J and n positive. The residue identification is the explicit iterated quotient, not an additional existence assertion.

Step 5 uses precisely the nilpotence clause of lem-weil-pbc-artinian-local-noetherian-nilpotent. A local map sends J^N into m_A^N=0, proving both finite-level factorization and continuity, even for a nonidentity residue map. This avoids assuming continuity before proving it.

Step 6 uses only steps 2 and 5 and elementary quotient factorization. A residue-compatible P-map kills q^N, so its extension is explicitly the Nth completion projection followed by the quotient map. The residue equation makes the extension local. Uniqueness uses surjectivity P→S/J^N, not surjectivity P→S. Thus no density argument or topological extension theorem is hidden here.

Step 7 cites def-weil-pbc-mv-polynomial-ring, whose statement explicitly includes evaluation's universal property, to choose lifts of all variables across B→A. The residue equation follows because B→A is a morphism in the marked test category. Step 6 extends the polynomial map and its injectivity proves the lift composes to the original map. This proves lifting for arbitrary surjections, without adding a square-zero restriction.

Checked delivery-errors B–E: there are no new statement-only nodes, no relabelled clauses, no unproved standard comparison, no unstated finiteness condition, no source-route substitution and no SGA citation. Every cited node's needed assertion is in its statement; citations.json quotes that text verbatim. The only non-Mathlib algebra tool from another unit is completion Noetherianity, declared in split_report.tool_uses for maintainer review. Each proof step is below 2000 characters; elementary steps are the explicit geometric-sum, quotient, and variable-evaluation calculations, not new theorem nodes.

Checked edge cases s=d=0 (P=R, including the case R=k and q=0), n=1 (the quotient is k), L=J, and A=k. A field k rules out a surjection from the zero ring. No restriction on characteristic, separability, injectivity of R→k, or finiteness of k as a set is used. Completeness of R is unnecessary. The condition e(X_i)=0 is retained but the lifting argument works for all variables and does not require their chosen lifts in B to be zero.

Dry-run repair: replaced the two short Noetherianity citation excerpts with the complete cited statements after the citation gate required at least 40 characters. No mathematical change was needed.
