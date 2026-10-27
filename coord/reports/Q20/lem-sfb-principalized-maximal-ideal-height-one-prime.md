## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-principalized-maximal-ideal-height-one-prime.json: statement, split; four proof steps, statement and statement dependencies unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-krull-principal-ideal-height-bound.json: statement, Mathlib leaf, Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes at Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:108-109.
- citations.json: verbatim statements supporting both proof citations.
- searches.jsonl: actual logged searches, reused in the JSON records.

Attachments: none. Searched lean/WeilConjectures/ for the item's blueprint tag, principalization and height-one terminology. The normal-domain principal-quotient associated-prime theorem assumes normality and concerns associated primes, so does not state this item. No matching project declaration was found. No Lean was written or compiled.

WANTED: none.

The imported statement is correct. Its proof was empty; the old searches already suggested the two algebraic ingredients but did not make the existence or contraction argument a split. I retained the old statement, provenance and searches and added the proof. The existing leaf lem-weil-pbc-minimal-prime-over-proper-ideal already gives existence without a Noetherian hypothesis. I reused it rather than creating an existence node. The new height bound is a general theorem for any Noetherian ring and any principal ideal, including zero and unit generators; it is not this item's existence/contraction assertion. The lower height bound and contraction are elementary steps, not new nodes.

All work is finished subject to the required dry run and push. The delivery tool's final result is the authoritative delivery record.

## Blueprint and search audit

Read the chapter and unit records and the newest blueprint at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/: _section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The current direct-image paragraph (3) assembles proper and open direct images along compactification. The inherited DAG ancestry locates this subordinate algebra input on its established local-domain/DVR route through Stacks 00P8. This split keeps that route, the item statement, and the existing null blueprint.from.node returned by tools/blueprint_refs.py ancestor. The new leaf uses the same ancestor and the item's via list with the item prepended. Neither chapter nor unit is edited.

Before creating the leaf I searched the entire DAG by principal-ideal/height/minimal-prime wording, by the Mathlib declaration, and by Tags 00P8 and 00KV. I also ran blueprint_refs.py search for principal ideal, minimal prime, 00KV, height, principal and the item's title. No imported blueprint node states the general principal ideal theorem. The title search and the principalization/height source search found no attachment for the item. The same-tag candidate statements are distinguished below.

For the new leaf, msearch.py ran LeanFinder and LeanSearch on the general Noetherian principal-ideal height bound, Loogle on Ideal.minimalPrimes, Ideal.height, and grep on height_le_one_of_isPrincipal in RingTheory. All four searches ran successfully and found the precise theorem. I read KrullsHeightTheorem.lean:46 and 105-116 and MinimalPrime/Basic.lean:40-47,93-96. The ambient Noetherian and commutative-ring assumptions are present. The singleton-span principal ideal supplies exactly the stated specialization. No second negative phrasing is necessary for this positive match. For the whole item, the additional semantic searches used local maximal-ideal/principal-extension phrasing, and grep checked height/comap/under/primes-over terminology. The hits do not provide the whole assertion under these hypotheses: Dedekind, finite-module and integral-extension results need extra assumptions, whereas Krull's theorem assumes an already supplied minimal prime. The original item's independent earlier searches have been retained.

## Not duplicates

lem-sfb-krull-principal-ideal-height-bound vs lem-sc-effective-cartier-affine-dimension-drop: the existing statement concerns dimension drop for a nonzero principal hypersurface in an integral finite-type algebra over a field; it neither states a height bound for primes of arbitrary Noetherian rings nor applies to the arbitrary domain S in the item.

lem-sfb-krull-principal-ideal-height-bound vs lem-sc-cartier-divisor-points: the existing statement decomposes an effective Cartier divisor on a smooth connected curve into point multiplicities; it does not state the general ring-theoretic principal ideal height bound.

lem-sfb-krull-principal-ideal-height-bound vs lem-sc-tsen: the existing statement is the C1 and Brauer-vanishing theorem for curve function fields; its source list happens to cite 00KV, but its statement does not give Krull's principal ideal theorem.

lem-sfb-krull-principal-ideal-height-bound vs lem-sfb-principalized-maximal-ideal-height-one-prime: the new leaf has no local subring, no maximal ideal extension, no existence assertion and no contraction assertion; it gives only the general upper bound. The item constructs its prime using the existing existence leaf and proves contraction and the lower bound explicitly.

## Review by Q20

I read the actual Stacks proof of 00P8 (algebra-lemma-dominate-by-dimension-1), especially the passage mS=x_r S, properness, choice of a minimal prime, height one and lying over m at algebra.tex:28913-28918. The item's hypotheses isolate precisely that passage. B need not itself be Noetherian for this extracted argument; S must be Noetherian for the height theorem. I read 00KV (algebra-lemma-minimal-over-1), part (1), and its proof at algebra.tex:14634-14658 for the new leaf. It gives height zero or one in arbitrary Noetherian rings, hence the upper bound actually stated. I read 00E0 (algebra-lemma-Zariski-topology), parts (2)-(4), at algebra.tex:2987 onward for the existing existence citation, and opened the cited DAG node itself.

Step 1 takes only minimal-prime existence from lem-weil-pbc-minimal-prime-over-proper-ideal. Its statement explicitly assumes a proper ideal and supplies a prime containing it with no smaller prime containing it; aS != S is exactly the required hypothesis. It supplies both primality and containment, rather than relying on something in its proof. citations.json quotes that complete statement verbatim.

Step 2 uses no non-elementary theorem. I checked that the contraction is an ideal directly, that it is proper because its membership would put 1 in q, and that every b in m_B maps into the extended ideal m_B S=aS. Maximality then forces equality. Neither a general integral lying-over theorem nor any assumption of integrality of S over B is used.

Step 3 cites only lem-sfb-krull-principal-ideal-height-bound. I opened its complete statement and verified that R=S, x=a and the prime from step 1 meet every hypothesis, including Noetherianity of S and minimality, and give exactly height at most one. Its quoted statement in citations.json is verbatim. The Mathlib declaration does not require a domain, a local ring, a nonzero generator or a proper principal ideal, so no hidden hypotheses are added.

Step 4 proves the lower bound without a lemma: the inclusion preserves a != 0, a belongs to q, zero is prime because S is a nonzero domain, and hence (0) < q is a chain of length one. The definition of height in the item makes the inequality immediate. Combining the two inequalities gives precisely height one. The minimality and contraction clauses remain those of steps 1 and 2. All steps have fewer than 2000 characters (largest 509), so none hides a long comparison argument.

I tested the item with B=S=k[t]_(t), a=t (q=(t)), and with S=B[u] (q=(t), still height one). A field B cannot satisfy nonzero a in its maximal ideal. Taking S=Frac(B) violates the explicit properness condition, so that excluded case causes no false existence assertion. For the new general leaf, x=0 in a domain gives the zero prime of height zero; a unit gives no minimal primes and the assertion is vacuous; and R=k[e]/(e^2), x=e gives a height-zero minimal prime. Thus the upper-bound formulation is correct without a domain condition, while the item's nonzero domain assumptions are exactly what justify its separate lower bound. Multiple minimal primes are harmless: the argument works for any chosen minimal prime.

Checked delivery-errors B through E against the JSON and sources: the only new node is a statement-only Mathlib leaf, introduces every object, defines height and minimality inline, and cites the existing Noetherian definition. Its source is the verified Stacks tag and label, and its match gives the file and read lines. Same-tag statements were read and distinguished above. The proof is an assembly with explicit elementary calculations, not a relabeling; every non-elementary fact is in a cited statement. No dependencies are taken from proofs, no new node cites the item, no SGA is used, no statement is weakened, and no unsupported source claim was found. I corrected the missing proof and dependency coverage, not the statement. The source/provenance and imported fields are preserved.
