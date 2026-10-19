# Worker report: thm-pur-regular-immersion-purity

## Files written

- `dag/nodes/sec-smooth-purity/thm-pur-regular-immersion-purity.json`: existing statement, now split into four applications of the existing same-unit theorem `sk-thm-regular`. No Mathlib match.
- `citations.json`: verbatim statement quotations for all eight step/node citation pairs.
- `searches.jsonl`: six actual msearch.py searches; no prior searches or split existed when this worker resumed.

New nodes: 0. Mathlib leaves: 0. The sandbox also contains the preparation script used to produce these artifacts; it is not a DAG delivery file.

## Attachments

None. I searched WeilConjectures for the exact blueprint tag and for regular-immersion purity, fundamental classes and the expected declaration name. The relevant file is `WeilConjectures/EtaleCohomology/Purity/Smooth/RegularImmersion.lean`. In particular `AlgebraicGeometry.Etale.isIso_fundamentalClassMap` (line 255), the etale restriction theorem (line 270), the exterior-product theorem (line 302), and `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_of_isRegularImmersion` (line 349) all have sorry proofs. They are not attachments. The last declaration alone would not give all clauses of this item anyway.

## WANTED

None. The current blueprint statement, detailed proof, unit statement and existing DAG theorem are available locally. This delivery uses no SGA source and no trace-based replacement of the diagonal/DNC route.

## What was wrong and what changed

The imported detailed theorem duplicates the existing unit theorem `sk-thm-regular`. Searching `tools/blueprint_refs.py search 'regular closed immersion'` found both and the surrounding regular-immersion nodes. The existing theorem has all four clauses, including the exact Kummer normalization and both compatibilities. It already records this item in its `blueprint.same_as`, and its independent review explicitly recommended merging the duplicate. I added the reciprocal same_as entry and used the existing statement instead of creating new lemmas for the same assertions. The maintainer may merge these two nodes; this worker does not change merged_into or another node.

The old proof used a definition for the exceptional composition law, a derived-tensor definition for cancellation, and a long final-class argument with unsupported normalizations. It also passed through `cor-pur-affine-space-purity`, whose current statement requires e|n. I removed that proof and its unused dependencies. All-level purity and the affine normalization remain on the existing `sk-thm-regular` route, so no ramification hypothesis is added here.

The item statement text is unchanged. Its statement dependencies now point to the actual setting, frame prescription and frame-independence assertion used by its text. I replaced the old `def-pur-regular-immersion` dependency, which explicitly limits c to positive integers, with `sk-def-purity-conv`, the unit's own regular-sequence convention allowing c=0. This repairs a stale definitional dependency rather than excluding the empty-sequence case from the source. Direct generic site and scheme-morphism-property dependencies are already provided by the fixed setting and are not independent notions introduced by the statement.

The item is not the unit's designated key node: the unit realization already names `sk-thm-regular`. No unit record was edited.

## Unfinished work

None for this one-level split. The theorem reused here remains a DAG dependency; this delivery does not claim that its Lean proofs or its entire descendant closure are finished.

## Not duplicates

No new nodes. Existing `thm-pur-regular-immersion-purity` vs `sk-thm-regular`: the latter is the unit theorem and states every clause of the former, plus explicit stalkwise generation and product-pair hypotheses. This is precisely why the proof reuses it. No new clause-node or wrapper lemma was created.

## Review by Q99

I read the full current main-20261015 detailed theorem and its proof, the unit statement from `sk-thm-regular/_section.md`, the complete DAG statement and proof of `sk-thm-regular`, and its recorded independent review. I also read `def-pur-conventions`, `sk-def-purity-conv`, `def-pur-frame-class`, `lem-pur-frame-independence`, and the old regular-immersion definition. The detailed theorem's imported blueprint_update has the same mathematical statement as its statement field. Every hypothesis and every conclusion occurs in the existing unit theorem. This is an existing duplicate, not a new node into which the item has been moved (D1/D2).

Step 1 uses exactly the statement of `sk-thm-regular` clause (a). Both conventions specify the finite ring A=O_E/varpi^n, k=Fq-bar, small pro-etale sites, and constructible exceptional inverse images on separated finite-type schemes. The unit convention's bounded constructible finite-Tor setting applies to the coefficient unit and its invertible twists. There is no ambient exceptional-adjoint hypothesis and no condition e|n. The regular-immersion, smooth-ambient and regular-source hypotheses are literally those of the item. The clause states concentration, rank one and supported cohomology, so none is inferred from a definition masquerading as a theorem (C4). Its quotation is copied into citations.json.

Step 2 uses `sk-thm-regular` clause (b), not its proof, for independence, existence, uniqueness and generation. I compared its displayed frame-class formula with the complete definition `def-pur-frame-class`: the individual Kummer boundaries, their supported ordered cup product and the unit for an empty frame are the same. The concrete coefficient prescription agrees because the unit convention allows N=n and states that the root-sheaf insertion is zeta -> zeta tensor 1; the frame definition uses the same inverse-limit projection-induced identification with mu_(ell^n) tensor A. This is identification of the specified maps, with no flatness assertion for A over Z/ell^n and no multiplication of G_m by A. I cite and quote the convention as well as the entire frame definition, so the coefficient comparison is exposed. No unproved purity theorem is hidden in this matching of definitions.

Step 3 takes both directions and the generator normalization directly from clause (c). In particular I did not invert the wrong affine-comparison map: the cited statement itself says that the inverse of cl_i(-c)[-2c] is Ri^!Lambda_X -> Lambda_Z(-c)[-2c]. The morphism is the one of Step 2 because clause (c) specifies its image of 1. No extra co-projection theorem is silently assumed by this application.

Step 4 uses clause (d), which states the etale base-change identity, the exterior-product identity, and that the product is again a pair of the stipulated codimension. Together with the canonical isomorphism in clause (c), these give the requested map compatibilities, not just existence of some isomorphisms. All four steps are non-elementary because their substance is an invocation of that existing theorem. Each is below 2000 characters, and no comparison lemma has been hidden in a long inline step.

I checked B1-B9: no new nodes or unspecified new sources, no new duplicate, valid TeX/JSON, no leaf claim, actual logged Mathlib searches, and reciprocal blueprint same_as recorded. The six searches cover LeanFinder in two phrasings, LeanSearch, Loogle and two source greps; the returned algebraic immersion/normalization and algebraic Kummer-theory hits do not assert etale cohomological purity. I checked C1-C8: every non-elementary assertion is a quoted clause of the existing theorem; this is in the same unit and needs no off-route tool declaration. A read-only traversal of statement and proof dependencies found no path from sk-thm-regular back to this item (14522 nodes visited), so the new dependency does not create a cycle. I checked D1-D5 by retaining the original theorem as an existing reusable result, with no new wrapper and no use of its proof as an unstated interface.

For E1-E7 I tested empty X or Z, c=0 (identity near Z, empty frame unit), the codimension-one origin in A^1_k (the Kummer-boundary normalization), a product with a codimension-zero factor, disconnected/non-equidimensional smooth X, and ramified E with n=1. These cases are covered by the same clause statements: there is no subtraction n-c on empty components here, no assumption that an etale chart is an isomorphism, and no freeness claim for A over Z/ell^(n/e) when e does not divide n. No assertion for an arbitrary singular regular immersion has been substituted for the required regular pair. The only corrections were the duplicate reuse, explicit matching of the finite coefficient/frame conventions, and cleanup of stale dependency edges described above. This is my direct-delivery self-review under the dispatcher's brief; no second worker was started.
