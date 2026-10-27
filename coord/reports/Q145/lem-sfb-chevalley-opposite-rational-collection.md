## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-chevalley-opposite-rational-collection.json`: item, statement, status split; seven-step agent proof, no Mathlib match. Exact original statement and statement dependencies retained. Five existing proof dependencies; no new nodes and no Mathlib leaves created.
- `citations.json`: one verbatim statement excerpt for every step/node citation.
- `searches.jsonl`: actual Q145 search-command log (five searches); the item's previous Q09 searches are retained in its JSON, with these new search results appended.

## Attachments

None. Searched `lean/WeilConjectures/` for the item tag, Chevalley, opposite root/exponential and big-cell terminology. There is no project declaration stating the item. No Lean written or compiled.

## WANTED

No additional source is required to check this assembly proof. The existing integral-PBW dependency records Steinberg, *Lectures on Chevalley Groups*, and Kostant, *Groups over Z*, as wanted for its own proof. I do not present Milne as a source of the formal collection identity verbatim.

## Problems in the item, blueprint, or brief

The item is an agent-formulated supporting local matrix lemma. Milne pp.510--511 supplies admissible lattices, (152), root polynomial (153), and Theorem 23.72, whose proof explicitly omits details. It does not state the requested local rational factorization. Thus the proof is marked `proof_origin.by = agent`, and the omitted details are supplied rather than attributed to the theorem. The parent open-cell statement and the generated group's reductivity are not used: either would risk circularity because the parent cites this item.

No statement dispute was found. The full-weight and weight-decomposition hypotheses are necessary to put the torus inside the prescribed diagonal blocks and make its coordinate algebra a quotient. Small characteristic is handled by proving coefficient identities over the integral PBW algebra before reducing to the field; there is no passage from a rational matrix equality through denominators divisible by the characteristic.

The inherited `blueprint.from.node` is null, and `tools/blueprint_refs.py ancestor` also returns null. I retained that value and the complete existing `from.place` and `via` chain, and filled the split report with the places it realizes. The latest blueprint (snapshot main-20261024) contains the enclosing six-functor direct-image proof, not this root-theoretic construction. No unit or chapter record was changed.

## Unfinished work

None for this one-level split. The cited closed one-sign-coordinate statement is now a separate existing split node; its current statement supplies exactly the closed embeddings used here. This delivery does not assert that all its dependencies have been formalized or proved in Lean.

## Not duplicates

No new node was created. Before deciding this, I searched the whole DAG and the whole imported blueprint with `blueprint_refs.py search` for opposite products, Chevalley, Kostant and Gauss, and inspected the existing root-normalization, integral rank-one, divided-power straightening, PBW, polynomial-coordinate and block-Gauss statements. The whole-DAG matches include the existing PBW and Gauss tools used below; a generic matrix transvection factorization is not an attachment of this item.

## Review by Q145

I read the standing stage-1 brief, the stage document, the three-level rule in SETUP.md, GOAL.md, the worker role, the chapter and unit records, and delivery-errors B through E. I also read the current latest blueprint chapter/unit and direct-image proof, and Milne's printed pp.510--511 (PDF text around equation (153), Theorem 23.72 and its Notes). The latter explicitly omits construction details, so I wrote the following assembly proof and marked it as agent-written.

For step 1 I opened `lem-sfb-root-base-rational-integral-spans` and `lem-sfb-kostant-integral-pbw`. The former says the simple coroots form a rational basis and generate the integral coroot lattice. The root system and simple-base hypotheses in this item give its perfect root-coroot pairing. The latter states the full ordered divided-power/binomial integral basis for any ordering of the positive roots, as well as the representation extension. These are the precise inputs for the coefficient calculation. I checked the coproduct formulas on each generator: divided powers split without binomial coefficients, and the Cartan binomials split by the polynomial Vandermonde identity. Multiplying in the prescribed PBW order gives the displayed multi-index splitting without reordering a tensor factor.

Step 2 is an explicit coefficient argument, not an additional black-box lemma: every parameter coefficient is a finite integral PBW sum; comparing the coefficient of Q_J tensor Q_K in the group-like identity gives c_(J+K) = c_J c_K. The augmentation gives c_0 = 1. This derives every coefficient as a monomial in the singleton coefficients and gives their vanishing constant terms. All formal series rings used in the proof are defined by their coefficient/convolution meaning. The proof does not assume that a general formal inverse is rational.

For step 3 I reread the PBW representation clause and the statement of `lem-sfb-chevalley-admissible-representation`. The representation's integral action follows because U_Z is generated by the divided powers that preserve Lambda. Each Cartan binomial acts by an integer on the stated weight lattice. I explicitly checked negative eigenvalues using binom(-k,m) = (-1)^m binom(k+m-1,m), so there is no hidden nonnegative-weight assumption. The formal torus point is the homomorphism lambda to the product of (1+z_i) raised to its integer coroot pairings; this specifies the weight-character torus, rather than the full block-diagonal group. The substitution is coefficientwise finite, since every singleton coefficient lies in the parameter ideal. This is also why reducing integral coefficients to F works in characteristics 2 and 3.

For step 4 I opened the entire statement of `lem-sfb-chevalley-unipotent-polynomial-coordinates`. It states both that p_+ and p_- are closed immersions onto closed subgroup schemes, and that their matrices are upper/lower block unitriangular in any separating positive weight order. All its hypotheses are copied verbatim into this item's statement. I give an explicit positive rational choice avoiding the finitely many weight hyperplanes. The torus inclusion is not taken from an unrelated definition: the entries and inverse entries map to e^lambda and e^(-lambda), which generate F[P] because Z Omega = P. This directly proves its scheme-theoretic closedness, including arbitrary test algebras.

For steps 5 and 6 I read `lem-sfb-block-gauss-scheme-chart`. It gives unique Gauss factors as morphisms on the principal open defined by the leading block minors, over every commutative algebra. I verified its hypotheses: the ordered blocks are exactly the nonzero weight summands, the polynomial g is invertible, and all leading minors equal 1 at zero. I choose the denominator to be their actual product, so its value is exactly 1, not merely nonzero. The map F[a,b,1/d] to F[[a,b]] is explicitly injective because d has constant term 1. Gauss uniqueness identifies the rational factors with the formal factors; closed-embedding equations then vanish in the localization itself. Finally the existing polynomial-coordinate statement provides the inverse coordinate isomorphisms onto U_+ and U_-. This is an equations-in-coordinate-rings argument and does not infer scheme factorization from set-theoretic image containment.

Step 7 checks normalization and universality directly. Every algebra-valued evaluation is induced by the localization homomorphism f/d^n to f(a,b)d(a,b)^(-n). Thus nonreduced algebras are included without any density-of-points argument. I tested the empty root system (V=P=0, T=1, d=1) and rank one. In the standard SL2 representation the construction gives d=1+ab, A=a/(1+ab), B=b/(1+ab), and h=diag(1+ab,(1+ab)^(-1)); direct multiplication verifies the orientation and the signs. The same formula is valid modulo 2 or 3 and on dual numbers whenever 1+ab is a unit. Weight multiplicities do not affect the argument: diagonal factors are scalar on each weight block, and uniqueness is block Gauss uniqueness. Product root systems and extra trivial representation summands likewise leave the coefficient comparison unchanged.

I checked every explicit uses entry against a verbatim portion of the dependency's statement, recorded in citations.json. No step cites a proof rather than its statement, and no new node is a renamed clause of the item. All five proof dependencies have the same unit; an explicit dependency traversal from each candidate back to the item found no cycle. Every proof step is below 2000 characters. All nontrivial inputs are cited; the remaining coproduct and formal coefficient manipulations, the surjection giving a closed torus, and localization descent are written out. I retained the exact target statement, source record and blueprint fields, and set proof_deps to precisely the union of step uses.

I ran the required Mathlib searches with the logged command (two LeanFinder phrasings, Loogle, LeanSearch and grep) and read their outputs. GeckConstruction describes root matrices/brackets; its statements do not give group factorization. The matrix transvection result allows unrestricted transvections and is only over a field. I read SchurComplement.lean lines 48--68: its two block identities do not give membership in the prescribed root subgroups or weight torus, so the item is not a Mathlib leaf. No search failure was recorded as a mathematical absence.

## Dry-run repairs

The first captured preflight rejected the phrase “the item's displayed identity” in step 6 as a self-containedness violation (B2). I replaced it by the full matrix identity in that step. No object or mathematical hypothesis changed.

## Repair of returned head 27d8d256d12 (Q145, 2026-10-24)

The return names one landing failure: the statement of `lem-sfb-block-gauss-scheme-chart` changed after the prior review. I continued the retained item, report, citations and five logged searches; I did not replace them with a fresh split. The required initial dry run exited successfully at 20f60b0d998. That alone did not discharge the return: I reread all five current proof-dependency statements and changed the application and its citation evidence before the final dry run. The delivery tool prepares the repaired commit on the current server DAG; no repository or launcher file was edited.

The current Gauss statement specifies a field F, a finite direct sum of nonzero blocks, the leading determinants for exactly that block order, and the principal open whose algebra-valued points make every determinant a unit. It gives an isomorphism of schemes and unique factors functorially over every commutative F-algebra. Step 5 now explicitly identifies E and every E_i, proves that these blocks remain nonzero over F, names the leading determinants, and writes an inverse for each determinant in the localization. Step 6 explicitly applies uniqueness over F[[a,b]], which is an F-algebra although it is not a field. Thus the use requires no field assumption on the test algebra, no conjugation-equivariance clause, and no assertion about arbitrary scalar-leading minors. Both Gauss entries in citations.json now quote the current unit-minor criterion together with the uniqueness clause.

I also reread the root-base statement (step 1: rational basis of simple coroots), integral PBW (steps 1 and 3: integral ordered basis and extension of the representation), admissible representation (step 3: integral divided powers), and one-sign polynomial coordinates (steps 4 and 6: closed immersions and upper/lower blocks). These current statements still supply the indicated facts under the hypotheses already in the item. In particular the coordinate node has since acquired split status, so I corrected the retained report’s obsolete description of it as unsplit. The PBW citation for step 3 now quotes its representation-extension sentence directly. Their proofs are not being used as additional hypotheses. I compared the retained item's statement, statement dependencies, provenance and blueprint fields with the live unsplit item; the repair preserves them. There is no released repair-note file requiring a different route.

I checked the Gauss applicability also for zero blocks count, one block, repeated weight multiplicities, and nonreduced algebras. If E is zero the empty product is 1, as in the cited statement; if there is one block, L and U are trivial and the chart is GL(E). For the root-empty case the root products are identity even if the chosen representation has a nonzero zero-weight summand, and its leading minors are all 1. No edge case adds a hypothesis. The PBW coefficient proof and closed-equation descent remain the previously reviewed route, and the revised steps remain below 2000 characters. No new nodes were needed, so the existing search question and its recorded results are unchanged.

For review reproducibility, these are SHA-256 hashes of the exact current statement strings I reread (not hashes of their evolving proof or review metadata):

- `lem-sfb-root-base-rational-integral-spans`: `c116b663f2e74eb5e37ed16ff6d8a6af69c40c1f57fb613fcbd01b6cf3a6cc86`
- `lem-sfb-kostant-integral-pbw`: `52617e7813b42b38bca571af84a8f018998db08ac5a6d34c34cb5c58a77b4564`
- `lem-sfb-chevalley-admissible-representation`: `0bdd476cd119de50425b6acdd52bb42c1f088fdfe7ee33fcd13ea33395c231bb`
- `lem-sfb-chevalley-unipotent-polynomial-coordinates`: `20f64dfe5e80e8455b3da82d1c0791912ef43b019232963ae614701cb29daa09`
- `lem-sfb-block-gauss-scheme-chart`: `66fe528c74a4f6e55d3e7a834a6cfb5adb5e0c2b076bc8b0dd7550d8c0e20a21`
