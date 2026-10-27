# Q38: lem-sfb-lci-polynomial-local-factorization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-lci-polynomial-local-factorization.json: six-step proof, statement and statement dependencies unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-koszul-immersion-smooth-lift.json: statement-only input, Stacks 067S, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-koszul-immersion-smooth-push.json: statement-only input, Stacks 0693, no Mathlib match.
- citations.json: verbatim statements for every step/node citation.

Two new nodes, zero Mathlib leaves. No Lean or unit records were changed; no compiler or build was run. All writes are confined to the sandbox.

## Attachments

None. The item id and Stacks label/tag have no match in lean/WeilConjectures. Concept searches found definitions of complete intersections over a field and smooth polynomial factorizations, but no theorem about arbitrary Koszul-lci scheme morphisms giving every clause of this item. The two new inputs likewise have no project declaration found by label, tag or concept.

## WANTED

None. All sources used are present locally.

## What changed and why

The statement is correct. I read more-morphisms.tex 069E (lemma-koszul-independence-factorization), the introduction and polynomial-factorization remark around 069F (definition-lci), and 069G (lemma-lci). I also read morphisms.tex 04II (lemma-quasi-affine-finite-type-over-S), and divisors.tex 067S and 0693, with their proofs. The construction follows the affine specialization of the polynomial remark. The comparison of smooth ambient embeddings is proved in the item using the two divisor inputs, exactly as in the proof of 069E.

The first dry run rejected a single new comparison node for 069E as too coarse. That sandbox-only node has been removed. The replacement exposes its two distinct inputs and writes the product-graph argument, including smoothness of both projections, in the item. This is a finer split of the source proof; no gate was altered. Smooth restriction and smooth ring base change reuse existing nodes instead of creating more nodes.

I read SETUP's three levels, the chapter and unit records, and the current latest blueprint's sk-thm-sf-ctf-stability/_section.md and direct-images.proof.md. The inherited historical alteration-prerequisite chain has no imported ancestor: blueprint_refs.py ancestor prints None. I preserve that from.node and via chain, give precise divisor-source places for both inputs, and explain the realization in split_report. Whole-blueprint searches for the two tags, smooth factorization, lift/push regular immersion, Koszul-regular and polynomial local found no identical blueprint node. This is a supporting scheme-theoretic argument; no chapter or unit route is replaced.

## Searches and leaves

Inherited item searches and their results are retained. For each new input I ran LeanFinder in two different phrasings and LeanSearch, and reused the actual logged Koszul/smooth Loogle query and Koszul-regularity source grep. Additional item searches were run. All searches are recorded exactly as in searches.jsonl; all services answered. Hits are smooth-chart descriptions, ordinary immersions, smooth composition, and formal lifting along nilpotent ideals, rather than statements about Koszul regularity of the two immersions in a smooth triangle.

I read Mathlib/RingTheory/Regular/RegularSequence.lean:21 (Koszul regular sequences are listed as TODO), the affine-local Smooth definition and chart theorem in AlgebraicGeometry/Morphisms/Smooth.lean, and the ordinary immersion factorization in Morphisms/Immersion.lean. A plain immersion theorem or a formally smooth ring lifting theorem does not specialize to either new input in one line. Both new nodes are therefore unsplit, with empty proof and proof_deps; neither is mislabeled a Mathlib leaf.

## Not duplicates

lem-sfb-koszul-immersion-smooth-lift vs lem-sfb-lci-polynomial-local-factorization: the new input preserves a supplied Koszul immersion when it is lifted to a supplied smooth ambient scheme; it constructs no polynomial embedding or target-open refinement.

lem-sfb-koszul-immersion-smooth-push vs lem-sfb-lci-polynomial-local-factorization: the new input descends regularity of a supplied immersion through a supplied smooth map, assuming that its composite is already an immersion; it gives no factorization or polynomial presentation.

lem-sfb-koszul-immersion-smooth-lift vs lem-sfb-koszul-immersion-smooth-push: the first assumes regularity of the composite and concludes regularity of the lift; the second assumes regularity of the lift and concludes regularity of the composite. They are the two distinct divisor lemmas in the proof of 069E.

lem-sfb-koszul-immersion-smooth-lift vs lem-per-regular-lci-geometric-calculus: the existing statement assumes Noetherian schemes and concerns ordinary regular immersions; the new input covers Koszul-regular immersions without that hypothesis.

lem-sfb-koszul-immersion-smooth-push vs lem-per-regular-lci-geometric-calculus: the existing statement assumes Noetherian schemes and does not state smooth push-through of arbitrary Koszul-regular immersions.

No existing node has either 067S or 0693 in its source. A whole-file tag grep also matches unrelated hexadecimal search digests; those are not source citations or statements of these lemmas. General scheme-theoretic smoothness inputs found in the DAG are cited directly in the item.

## Review by Q38

For the item I read all of Stacks 069E--069G and its polynomial-factorization discussion. For the two new inputs I read divisors.tex lemma-lift-regular-immersion-to-smooth (067S) and lemma-push-regular-immersion-thru-smooth (0693), including their proofs, and verified the tag/label mapping in tags/tags. Each new statement introduces Z,P,S, the three morphisms and their commuting triangle, requires BOTH source maps to be immersions, and requires the intervening morphism to be smooth. In 067S it is the composite which is assumed Koszul-regular; in 0693 it is the lift. Neither lemma assumes a Noetherian base. The latter's Koszul-regular case must not be confused with the ordinary-regular case, which it does not assert. The expanded local ideal meaning of Koszul-regular uses the same finite-sequence definition as the item, with lengths allowed to vary.

Step 1: def-sbc-smooth-morphisms gives the affine-local smooth ring description (including finite presentation), def-weil-pbc-finitely-presented-algebra spells out its polynomial quotient, and def-weil-closed-immersion gives the full affine quotient B/I. I added the existing lem-weil-pbc-smooth-restrict-open-subschemes(a) for W to T rather than hiding the restriction theorem. I checked its hypotheses: W and T are open subschemes and p(W) is contained in T. T is chosen INSIDE the prescribed V. Z is the full inverse image of W under the original closed immersion and is therefore affine and an open source neighbourhood. No claim that arbitrary affine intersections are affine is needed. Restricting the original ideal on W retains its local Koszul-regular generators.

Step 2: the three cited definition statements give respectively the surjective-ring-map criterion for a closed immersion, the affine coordinate formula for relative affine space, and contravariant functoriality of Spec. The polynomial map is explicitly A[t] to B to B/I, so it is surjective. Its constants map verifies the factorization over T. No unproved regularity of this new kernel is assumed.

Step 3: def-sbc-affine-space identifies Q as Spec(B[t]). The map to B/I is written on constants and variables; it is surjective on constants, so the cited closed-immersion criterion applies. The Spec functoriality citation justifies the two composite identities. The existing sbc-lem-affine-space-smooth states smoothness for EVERY base scheme and n >= 0, and applies to q:Q to W. This supplies the graph immersion without an uncited assertion about diagonals, separatedness, or product immersions.

Step 4: the new lift input applies with P=Q and S=W. I checked all hypotheses against its statement: c and j|Z are closed immersions, q is smooth, qc=j|Z, and the composite j|Z has the original Koszul regularity. The conclusion is precisely regularity of c.

Step 5: the existing lem-weil-pbc-smooth-ring-map-base-change-composition(1) states smoothness after ANY ring base change. I checked that R=A, S=B and R'=A[t] meet its hypotheses. The isomorphism A[t] tensor_A B = B[t] is written in both directions on monomials, so it is not an unexplained identification. Via the affine-local smoothness description in the cited def-sbc-smooth-morphisms this proves that r is smooth. The new push input is then applied with P=Q and S=A^n_T. Both c and b are closed immersions, rc=b, and c was proved Koszul-regular in Step 4. Its conclusion is exactly regularity of b on all of Z. In particular the final proof needs no unsupported source-shrink argument.

Step 6: def-sbc-affine-space identifies A^n_T with the preimage of the open T in V. Its inclusion is an open immersion by the actual open-immersion definition (topological open subset and restricted sheaf). The closed-then-open definition of immersion gives the required a with U=Z. The local ideals are unchanged in the open target A^n_T, so the regularity just proved is exactly the required regularity of a. The constants-map identity from Step 2 yields the composite to V and Y. This is an open restriction, not an assertion of preservation of Koszul regularity under arbitrary base change.

The three generic off-unit inputs (smooth restriction, smooth ring base change, affine-space smoothness) are declared in split_report.tool_uses. I checked their actual statements as above, not their proof internals. All citations.json quotes are verbatim parts of those statements or the two new statements. Against delivery-errors B--E, both new statements are self-contained, have only statement dependencies, use exact Stacks tags and labels, and are genuine lower-level inputs rather than clauses of the item. The proof has no forward inference or circular citation. Every non-elementary step cites its needed theorem, and the polynomial constructions remain written-out steps, not new nodes. All six steps have fewer than 2000 characters. Neither new node can depend back on the item: each cites only the four pre-existing definition nodes.

Small cases: empty source makes the pointwise assertion vacuous; n=0 gives Q=W and A^0_T=T; the identity immersion has the empty Koszul sequence. The nonflat regular quotient Spec(Z/2) to Spec(Z) is allowed because no flatness of the source is used. Variable ambient dimensions cause no uniform-rank assumption. To test the smoothness hypothesis, the embeddings of Spec(k) into A^1_k and into Spec(k[e]/e^2) have different regularity, but the latter ambient is not smooth and is excluded. The new lemmas and item retain Koszul regularity rather than replacing it by ordinary regularity in the non-Noetherian case. I found no statement dispute or source error to correct.

## Unfinished work

Only the two new statement-only prerequisite nodes remain for later splitting, as required by this one-level delivery. No part of the item's six-step assembly is deferred. The delivery tool records dry-run and push results.
