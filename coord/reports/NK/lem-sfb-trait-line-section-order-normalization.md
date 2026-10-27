# Stage-1 delivery: lem-sfb-trait-line-section-order-normalization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-trait-line-section-order-normalization.json`: statement, now split into nine proof steps; no Mathlib match for the whole item.
- `citations.json`: fourteen verbatim quotations, one for each node use in each step.
- `searches.jsonl`: actual msearch results; the item's inherited searches have also been retained.

New nodes: 0. New Mathlib leaves: 0. All non-elementary inputs were already in the DAG. The prime-power induction, germ shrinking, gluing, and evaluation are written in the proof rather than turned into new nodes.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag and uniformizer/section terminology found no declaration stating the whole item. The existing smooth-trait-affine-generic-open declaration was read, but it supplies a chart rather than the line-section normalization and all its clauses, so it is not an attachment for this item.

## Literature wanted

WANTED: Bosch–Lütkebohmert–Raynaud, *Néron Models*, §4.3, printed p.104 (PDF p.110), for lem-sfb-trait-line-section-order-normalization; the local literature copy named by the inherited source is absent. I read the primary scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf, including the page image. Its normalization paragraphs supply the intended conclusion and evaluation formula. The proof is marked agent-written because I expand the equal-component extension by the local prime calculation, rather than claiming the book contains this expanded proof verbatim.

## Problems and changes

The statement is unchanged; no STATEMENT-DISPUTED issue was found. In particular, neither irreducibility of all of Z, separatedness, residue-field perfection, nor completeness is needed. The stipulation about the DVR at each special-component generic point is used exactly where orders are compared. Generic-only components are covered by the already supplied generic frame.

The item was unsplit with an empty proof, no sandbox item, and no released repair note. Its inherited blueprint chain has `from.node = null`; `tools/blueprint_refs.py ancestor` likewise reports None. I retained that chain and its precise BLR place rather than inventing an imported ancestor. I read the current `literature/blueprint/latest/` unit file and the recorded chapter/unit. Whole-blueprint searches for `uniformizer`, `vertical order`, and `line-bundle frame` found no blueprint node with this statement; `same_as` remains empty.

## Mathlib and DAG search results

I read the inherited search evidence, ran both whole-item and local-algebra searches through msearch, and tried a second phrasing. LeanFinder's generic-trivialization query returned topological vector-bundle results, `Scheme.germToFunctionField`, and `ModuleCat.Tilde.isUnit_toStalk`; these do not extend a generic algebraic line frame. The Loogle query `"Scheme", "IsUnit"` returned `ord_of_isUnit` and `ordHom_of_isUnit`, whose source I read in OrderOfVanishing.lean: they give the order of an already regular unit, not the converse extension. The local-algebra search returned Away.algebraMap_isUnit_iff, Away.surj, and exists_reduced_fraction'; I read the localization sources, but they are ingredients, not a one-line specialization proving the item. LeanSearch also returned AtPrime unit detection and the DVR factorization class. The second grep found `dvd_prime_pow`; I read its source and retained its short prime-element induction as an elementary step, instead of creating a node for it. All searches recorded in this worker's added mathlib_searches are actual log entries. No new statement-only node needed searching or duplicate adjudication.

## Review by NK

I read delivery-errors B through E, the item's statement, and the statement of every node cited below. For the source, I checked BLR p.104 as described above. I also read Stacks algebra.tex at 00PD (lemma-characterize-dvr), 00NP (lemma-regular-domain), 07NF (lemma-regular-goes-up), 00T4 (lemma-base-change-smooth), 00TT (lemma-characterize-smooth-over-field), and 00TA (lemma-smooth-syntomic), morphisms.tex at 01V6 (lemma-smooth-characterize), and schemes.tex at 0HA1 (lemma-local-ring-fibre). I read the cited Mathlib flat-tensor injection declaration in RingTheory/Flat/Basic.lean. No new nodes were created, so there are no new-node sources to audit.

Step 1 uses lem-weil-pbc-dvr-unit-times-uniformizer-power only for factorization of nonzero elements, def-weil-regular-scheme for the regularity criterion, and def-pc-base-change for the fibre product. I write the denominator argument and the two-prime calculation explicitly: these show both E=R[1/pi] and regularity of the DVR without asking a definition node to supply an unstated theorem. The affine tensor-localization identification is justified by its universal mapping property.

Step 2 uses lem-weil-pbc-smooth-ring-map-iff-smooth-affine to pass to smooth affine coordinate maps, lem-weil-pbc-regular-ring-smooth-ascent for regularity, and lem-weil-pbc-smooth-ring-map-flat for flatness. R is regular by Step 1. Crucially, it also cites lem-trf-flat-tensor-preserves-injection for preserving the particular injection given by multiplication by pi; I did not cite merely the definition of flatness. The flat module in that theorem is B over R. Cancellation after localization then proves injectivity of restriction.

Step 3 uses lem-sbc-scheme-fibre-stalk-quotient for the actual quotient A/pi A, lem-weil-pbc-smooth-fibre-regular-local at the closed prime of R for its regularity, and lem-sc-regular-local-domain on both A and its quotient. Both rings really are regular local, and the point lies in the special fibre, so the quotient is not the zero ring. Affine stalk localization, from lem-weil-pbc-affine-open-stalk-localization, gives the ring identifications and their maps. The unique component through z and the identification with A_(pi) are explained by minimal primes and the explicit iterated fractions. This avoids assuming that the total scheme or the whole special fibre is irreducible.

Step 4 uses the Zariski rank-one clause of def-sc-invertible-module and the principal-open localization clause of lem-weil-pbc-spec-module-tilde-sections. It uses the latter's explicit structure-ring equality O(D(r))=B_r. I explain why a coefficient whose germs all generate is a unit by gluing inverse germs. Both f and its inverse are then actual fractions in A[1/pi], and the equality bc=pi^(r+t) is an equality in A because Step 2 proved injectivity.

Step 5 is the elementary induction on the exponent in that equality, with base and both induction branches written. The primality used here was proved in Step 3; no factoriality of A is assumed. Its application gives f=u*pi^(j-r), and the defining order condition at the corresponding component generic point gives j-r=n. Thus no new node merely restates the desired extension.

Step 6 supplies the previously implicit shrinking calculation. I checked both signs of q+n: with a=max(q+n,0) and b=max(-q-n,0), the equality pi^a*u=pi^b*d is exactly u=pi^(-n)*d/pi^q after localization. Its equality as germs spreads to a neighborhood, as does the equation making u a unit. This establishes the claimed equality with the prescribed generic section, not just existence of some local generator.

Step 7 uses the nonzerodivisor restriction property from Step 2 on an affine cover of every overlap; intersections themselves need not be affine. The sheaf axiom then gives the section and uniqueness. I checked the empty-special-fibre case separately: the generic open is then all of Z, so every integer is permitted, including for empty Z.

Step 8 reuses the stated DVR factorization on a numerator and denominator at the stipulated generic-point DVR. The fraction is nonzero because a is a generic unit. This gives existence of its integer order, while noninvertibility of a positive uniformizer power proves uniqueness. With one special component, the preceding argument applies. This checks every hypothesis of the final specialization.

Step 9 pulls back the global unit and its inverse. No assertion that an arbitrary map on points preserves an order is used: the explicit equality in Frac A and v_A(pi)=1 give the value. It works for ramification index one precisely because pi is assumed to be a uniformizer in A. I checked m negative, zero and positive.

For B1--B10, there are no new nodes, no copied proofs in statements, no unsupported Mathlib leaves, and all existing statement/source/blueprint data were preserved. For C1--C8, every non-elementary input has a cited existing statement, quotations were checked as literal substrings, generic tools from other units are declared under split_report.tool_uses, and the server checks will test dependencies and cycles. For D1--D5, the actual local calculation and gluing live in the item rather than a renamed clause. For E1--E7, all base rings, quotients, maps and units have been tracked, and the source assertion survives the edge cases above. No step exceeds 2000 characters (the longest is 970), and no source called standard is silently substituted for a cited theorem.

## Not duplicates

No new nodes. Existing results, including the regular-local-domain and smooth-fibre-regularity nodes found by tag and concept searches, were reused rather than duplicated.

## Unfinished work

None in the mathematical split. The first dry run required quotations of at least 40 characters for two citations; I replaced the short excerpts with the complete existing statements, without changing the proof or its uses. The server review_split check passed. Final dry-run and push results follow from the delivery tool.
