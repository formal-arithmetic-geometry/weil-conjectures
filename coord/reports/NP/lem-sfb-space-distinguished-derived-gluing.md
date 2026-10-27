# NP stage-1 delivery: lem-sfb-space-distinguished-derived-gluing

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-distinguished-derived-gluing.json`: statement, now split into eight proof steps; not a Mathlib leaf.
- `citations.json`: 22 step/node entries, each quoting the cited statement verbatim.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The statement and its statement dependencies are unchanged. Only the sandbox was written; no Lean, compiler, Lake, repository git command, or launcher modification was used.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag and distinguished-square/derived-gluing concepts. Its many scheme two-open Mayer–Vietoris modules do not state the algebraic-space assertion for arbitrary unbounded structure-sheaf complexes. No exact project declaration was found.

## Literature

No WANTED documents. Read `literature/stacks-project/spaces-perfect.tex`: definition-elementary-distinguished-square, Tag 08GN (lemma-make-more-elementary-distinguished-squares), Tag 08GV (lemma-exact-sequence-lower-shriek), Tag 08GW (lemma-exact-sequence-j-star), Tag 08H9 (lemma-mayer-vietoris-hom), Tag 08GG (lemma-pushforward-with-support-in-open), and Tag 08HB (lemma-glue), including their proofs. Read the restriction and extension-by-zero adjunction arguments in `sites-cohomology.tex`, lemma-restrict-direct-image-open and lemma-adjoint-lower-shriek-restrict. Read the generic triangle statements/proofs in `derived.tex`: Tags 0149 (lemma-representable-homological), 014A (lemma-third-isomorphism-triangle), 0152 (lemma-derived-canonical-delta-functor), and 05QR (lemma-third-object-zero).

The proof is recorded as agent-written because its assembly is an explicit supported-fibre variant of 08HB rather than a transcription of its homotopy-pullback construction. The geometric excision and all comparison inputs are unchanged: the fibre Q of B → Rk_*(B|T) is supported off T; its direct image H is zero on U and has counit p*H ≅ Q; attach H to Rj_*A using the transpose of the specified overlap isomorphism. This exposes the boundary compatibility as a counit equation before TR3 is applied. The final map-to-M argument is exactly the 08H9 proof via 08GV and Hom exactness, assembled from existing nodes.

Read the chapter and unit records, SETUP's three-level restrictions, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its `sk-thm-sf-ctf-stability-direct-images.proof.md`. This support item belongs to the existing perfect-limit-descent chain recorded in `blueprint.from.place`. It does not change the direct-image route above that chain. `tools/blueprint_refs.py ancestor` returns None for this created-node chain; its existing null ancestor and detailed place/via data are preserved. Blueprint searches for 08H9, 08GW and distinguished square found no imported blueprint counterpart. A broad gluing search and DAG tag/concept searches located the existing tools reused here, rather than new nodes.

## What was wrong or changed

The imported item was a statement-only node, not an accepted split. Its statement agrees with both assertions of 08HB plus 08GN(2); no statement dispute or weakening was needed. The proof now explicitly checks the reduced complement after base change, the support hypothesis for excision, the attaching boundary, the required overlap isomorphism, and the exactness needed for a map to a fixed M. It does not infer a morphism of arbitrary cone completions without checking the attaching square.

The existing lem-pc-derived-mayer-vietoris-triangle is only for qcqs schemes, quasi-compact open covers and quasi-coherent cohomology, so it is deliberately not used for this unrestricted algebraic-space statement. Likewise no classical underived sheaf gluing result was substituted for derived gluing.

## Mathlib searches

Preserved the item's earlier search records and read their recorded hits. Also ran the required logged command in this sandbox with LeanFinder, Loogle, grep and LeanSearch, and a second LeanFinder phrasing. Exact query texts and outcomes are in the item and `searches.jsonl`. No unavailable service was recorded as a negative result. The grep has two documentation hits (Mathlib/CategoryTheory/Sites/MayerVietorisSquare.lean:39–40), not zero: that file describes Nisnevich squares and constructs a free-abelian-sheaf short complex. Read its introduction and the returned signatures. Those declarations, generic GlueData and localization of complexes do not supply this derived module gluing theorem in one line. The second LeanFinder search returns MayerVietorisSquare.shortComplex/exact and isPushoutAddCommGrpFreeSheaf, likewise not a match.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. Reused lem-sfb-space-supported-etale-excision, lem-sfb-space-derived-etale-chart-calculus, lem-sfb-space-elementary-shriek-exact and generic existing triangle statements. Searched the whole DAG for 08HB, 08GN, 08H9, 08GW, supported excision, and distinguished-square/Mayer–Vietoris concepts before deciding this.

## Review by NP

I read 08HB against the item clause by clause: U is open, p is representable etale and isomorphic over the reduced complement; A and B are arbitrary unbounded O-module derived objects with the displayed overlap isomorphism. The target M and the two maps have exactly the compatibility required in the source. Neither 08HB nor the reused excision theorem requires perfectness, quasi-coherence, boundedness, quasi-compactness or separation. The universal base-change assertion comes from 08GN(2), not from an invalid assumption that the pullback of a reduced closed subspace is reduced.

In step 1 I opened lem-sfb-space-reduced-closed-support: it explicitly gives the support of the pullback closed subspace and explicitly warns that the pullback need not be reduced. On an atlas, taking the radical of its ideal gives the new reduced complement and hence a factorization into the pullback closed subspace. Restricting the base-changed isomorphism along that factorization proves the needed isomorphism over the new complement. The open-subspace definition is stable by the very fibre products in its statement. The etale-permanence statement explicitly allows arbitrary base change. This is the elementary reduced-ideal verification of the omitted proof of 08GN(2), not a separate geometric lemma being assumed.

In step 2 I opened the full derived-etale-chart-calculus statement. Its etale restriction is exact, its direct-image base-change holds for every unbounded K, and its composition comparisons respect units and counits. Self-base-change of an open immersion gives its restriction counit isomorphism. The cone formula in the derived-category definition explains preservation of triangles by exact restriction. TR1 and rotation supply the triangle of the specified unit B → Rk_*C. The zero-cone theorem applies after restriction because the triangular identity makes k*u an isomorphism. This proves the actual hypothesis k*Q = 0 required in step 3.

In step 3 the supported-etale-excision statement gives exactly both facts used: j*Rp_*Q = 0 and the specified counit p*Rp_*Q → Q is an isomorphism. The new object Q, not B, satisfies its support hypothesis. The chart-calculus adjunction and etale base-change supply the isomorphism v and its unique transpose s; the composite defining beta is written explicitly. Completing beta gives F by the triangulated-category axioms. No new hypothesis on X or B is introduced.

In step 4 the same excision vanishing and the open counit identify j*F with A, using the zero-cone statement after rotation. In step 5 I checked the last square before invoking TR3: e[1] p*beta = delta v follows by counit naturality and the transpose equation. Only then are the endpoints completed to a triangle morphism. The statement of lem-sf-triangle-morphism-iso says precisely that two invertible components force the third to be invertible; e and v are the two endpoints already verified. This avoids the common error of assuming arbitrary triangle completions have the required boundary compatibility.

In step 6 the square ug = v p*r is restricted to T. The inverse-counit identity eliminates u; the unit/counit-compatible base-change identifies the other side with c composed with f|T. Thus it proves the specified compatibility, not just an unspecified overlap isomorphism. These are naturality and triangular-identity calculations from the cited chart-calculus statement and the definitions of s, v and f.

In step 7 I opened the whole elementary-shriek-exact statement, including the signs and evaluation counits. It gives a degreewise short exact sequence for any representative of F, without support or compactness assumptions on F. The existing complex-ses-triangle statement turns precisely that sequence into a triangle. The exact functors and their adjunction units/counits descend through localization because they preserve quasi-isomorphisms, yielding the derived extension-by-zero adjunction directly. The statement of hom-out-of-triangle-exact (i) is exactly the factorization used after precomposition with the signed overlap arrow. Thus its kernel condition is equality of the two actual restrictions. In step 8 substituting (af,bg) makes that difference zero by the given a|T = b|T c and the compatibility proved in step 6. The lift gives both required restrictions of d.

I checked B1–B10: no new unsplit statements or duplicate nodes, all objects introduced, no missing new terminology, actual Stacks tags/labels, logged searches, unchanged statement, and preserved blueprint metadata. I checked C1–C8 by opening every cited node's statement, not its proof; citations.json uses those exact statements. Cross-unit geometry and triangle results are declared as tools in split_report, without self-approving top-level tool_uses. Definitions need no route override. I checked D1–D5: the steps construct F and d, no clause is moved to a new lemma, and the base-change omission in 08GN is filled with the reduced-ideal argument. I checked E1–E7 against the actual hypotheses, signs, objects and adjunction maps. No source error was found.

Small cases: if U = X, Q vanishes and F is Rj_*A = A; the isomorphism c identifies the prescribed B on V. If U is empty, T is empty and p is an isomorphism; Q = B, J = 0, and F = Rp_*B. The empty space and zero complexes give zero objects throughout. A nonflat or nonreduced W' is permitted because the support check uses reduction after base change, and the derived arguments require only etale restrictions. No proof step exceeds 2000 characters; all are explicit assembly steps, with no hidden standalone comparison lemma.

## Unfinished work

None in this stage-1 split. No new unsplit obligations were needed. Maintainer independent mathematical review remains the normal next review after direct delivery.
