# Stage-1 report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-complete-local-cotangent-graded-rigidity.json: statement, split; no whole-item Mathlib match. Its original statement, provenance, blueprint fields and inherited searches are retained. Added six proof steps, exact dependency union, fresh recorded searches and split report.
- citations.json: one verbatim statement quote for every step-node citation.
- No new DAG nodes and no new Mathlib leaves.

## Attachments

None. Searched the live WeilConjectures source for the item id, complete-local/cotangent/graded-rigidity notions, and relevant surjectivity declarations. No project declaration supplies both clauses. Mathlib's complete-source lifting result is already a DAG dependency, not an attachment.

## WANTED

None.

## Corrections and route

No statement dispute and no statement change. Read Stacks formal-defos.tex Tag 06GZ, lemma-surjective-cotangent-space, and artin.tex Tag 07XH, lemma-approximate-versal. The former uses Artinian truncations and Mittag-Leffler exactness; the latter uses equal lengths of truncations. The split implements those two ring-theoretic passages through existing general-purpose DAG lemmas: Nakayama plus complete-source lifting, then dimension additivity on graded kernels plus completeness. This avoids silently assuming a coefficient field or a common Noetherian coefficient base.

The nearby lem-sfb-complete-local-cotangent-surjectivity was read in full. It assumes complete local k-algebras with specified structure maps and is therefore not applicable to arbitrary mixed-characteristic C and D. No copy of it was created. Searched the whole DAG by cotangent, 06GZ, 07XH, rank-nullity, equal dimensions, and the relevant Mathlib declarations; read the whole-blueprint search outputs for cotangent, Nakayama, graded and surjective. Existing generic linear-algebra nodes suffice, so the matching Mathlib linear-map theorem was not made into a duplicate leaf.

Read the chapter and unit records and the current latest blueprint sk-thm-sf-ctf-stability-direct-images.proof.md. This is a supporting commutative-algebra item in the inherited alteration/moduli/Artin chain, not the unit's key statement; no realized fields change. The inherited nearest blueprint ancestor is null, as confirmed by blueprint_refs.py ancestor, and its precise nonempty from.place and via chain are retained. No same-statement blueprint node was found, so same_as remains empty.

## Unfinished work

None in this one-level split. Downstream formal proofs remain stage-3 work. No Lean written and no compiler or Lake invoked.

## Review by NG

I checked B through E of delivery-errors against the statements and source text. There are no new unsplit statements, elementary auxiliary nodes, clause-restatement nodes, unrun searches, or SGA citations. All six steps are shorter than 2000 characters. The item is not declared a Mathlib leaf: the matching complete-source theorem needs the extended-ideal equality, and the linear-map criterion alone cannot prove the ring statement. The fresh service outputs were read, and the queries in the item reproduce the actual log. Earlier Q07 search records remain intact.

For step 1 I checked that cotangent surjectivity gives n = mD + n² directly; no Nakayama or finiteness is hidden there. Step 2 cites def-weil-pbc-noetherian-ring, whose statement says every ideal is finitely generated, and lem-weil-pbc-nakayama-jacobson, whose statement is precisely IM=M for a finite module and I in the Jacobson radical. The quotient of the finitely generated ideal n is finite, n is the unique maximal ideal and hence the radical, and n(n/J)=n/J. I read algebra.tex Tag 00DV, lemma-NAK (2), as well as Mathlib Nakayama.lean lines 112-123; the cited statements justify J=n.

For step 3 I read the statement of lem-weil-pbc-complete-source-surjective-mod-ideal and its exact Mathlib source Functoriality.lean lines 447-459. It requires source precompleteness, target Hausdorffness for the EXTENDED ideal, and surjectivity modulo that ideal. Step 2 supplies mD=n; the bijective completion map in def-weil-pbc-adic-completion supplies precompleteness of C and Hausdorffness of D; the identity residue-field map supplies the last hypothesis. The completion definition was opened and read, and its whole statement is quoted in citations.json. No unproved exactness-of-inverse-limits fact is used.

For step 4 I checked the actual maps: locality says f^{-1}(n)=m, so after surjectivity every n-element lifts inside m. Writing powers as sums of products gives f(m^j)=n^j. The degree-zero case uses surjectivity, not a nonexistent coefficient-field section; the map on each quotient is k-linear because the residue map is the identity. These are finite-sum calculations from the definition of an ideal power.

For step 5 I opened both lem-trf-vector-space-quotient-dimension and lem-trf-finite-dimensional-short-exact-dimension. The former explicitly gives finite-dimensionality of any subspace of a finite-dimensional space, used for K_j. The latter explicitly gives dimension additivity for an injective first map and surjective last map with the specified kernel. Step 4 supplies that surjectivity. The grading spaces are finite-dimensional as in the hypothesis; independently, finite ideal generators give finite spanning sets after passing to residue-field quotients. Thus all three terms meet the cited additivity lemma's hypotheses. Equal finite dimensions force dimension K_j=0; an empty basis forces K_j=0. No general first-isomorphism theorem is silently required. Both exact statements were copied verbatim into citations.json.

For step 6 I verified the induction starts at m^0=C, including j=0 where g_0 is the identity residue map. Injectivity of g_j makes a kernel element in m^j lie in m^{j+1}. Completion injectivity (the cited definition) then kills it. A bijective ring map has ring-homomorphic inverse by checking the operations through f. This is the elementary separatedness consequence of the definition, not an invocation of Krull intersection.

Small cases checked: fields (m=n=0) give the specified residue isomorphism; k[ε]/(ε²)→k is cotangent-surjective and surjective but fails the equal-dimension hypothesis in degree one; k[[t]]→k[[t]]/(t²) agrees in degrees zero and one but fails in degree two, so checking every degree is necessary. Z_p→F_p is a mixed-characteristic instance of the first clause, confirming why a k-algebra hypothesis cannot be imported. Nilpotent maximal ideals and zero graded pieces cause no induction exception. The zero ring is excluded by the residue-field hypothesis and the existence of a maximal ideal. No excellence or characteristic restriction was used.

I checked every citations.json quote is a literal substring of the cited live node's statement, every uses list matches proof_deps, and no dependency has a path back to this item. The off-unit lemmas are generic ring lifting, Nakayama and vector-space dimension tools, each explained in split_report.tool_uses; no unit route is replaced.

## Not duplicates

No new nodes.
