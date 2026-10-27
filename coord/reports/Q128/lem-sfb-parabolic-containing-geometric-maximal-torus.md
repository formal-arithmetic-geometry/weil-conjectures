# Q128 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-parabolic-containing-geometric-maximal-torus.json`: statement, now split; no Mathlib match. Statement and statement dependencies unchanged. Four proof steps, all dependencies already present in the DAG.
- `citations.json`: one verbatim statement excerpt for each node used by each numbered step.
- `report.md`: this report.

There are 0 new nodes and 0 Mathlib leaves. `source/milne.txt` is a local reading aid, not a delivery file. The search command produced `searches.jsonl`; its five searches were read and recorded exactly, preserving the inherited searches as well.

## Attachments

None. The live `lean/WeilConjectures/` search for the exact blueprint tag, parabolic, maximal-torus and geometrically-maximal terminology found no declaration stating the item. Borel--Moore results concern another notion. No Lean was written or compiler invoked.

## Literature wanted

None. All mathematical source material used is present as `literature/milne-algebraic-groups_iAG2017.pdf`.

## What needed correction

The item's proof was empty. Its statement is correct and remains unchanged. The supporting facts already have nodes: in particular `lem-sfb-maximal-torus-field-extension` states exactly Milne 17.82. I avoided creating a duplicate maximal-torus existence lemma: bounded dimension and strict dimension growth make the choice retaining D an elementary argument using existing nodes. I also avoided creating a parabolic-Borel lemma, since the fixed-point and quotient statements already give its proof in one short step. The source's 25.1 maximal-torus choice is thereby justified without using cocharacter descriptions or Levi decompositions, which would risk depending on the parent.

The inherited blueprint.from.node is null, as `tools/blueprint_refs.py ancestor` itself reports, although its long place and via chain point back to det-thm-sf-ctf-stability-direct-images. I preserved that inherited provenance, filled no invented ancestor, and described the actual current-blueprint place in split_report.blueprint. Searches of the whole imported blueprint for `parabolic`, `maximal torus` and `maximal tori` found no duplicate. I read the latest blueprint's six-functors-basics chapter, sk-thm-sf-ctf-stability unit and its direct-images proof (3), together with the stored chapter and unit records. This lemma supplies a subordinate algebraic-group prerequisite of that route; no chapter or unit route is changed.

## Unfinished work

None in this one-level split. Existing dependency proofs retain their own independently tracked stage status. No new unsplit obligations are introduced.

## Not duplicates

No new nodes. Reused the existing maximal-torus field-extension, Borel conjugacy, Borel existence, solvable fixed-point, quotient geometry, torus smoothness and dimension statements after searching the entire DAG and blueprint. The item itself is not replaced by a clause restatement.

## Review by Q128

I read Milne 17.82 and Corollary 17.83, printed p.379, including the arbitrary-field theorem and its distinction between a k-maximal torus and its geometric scalar extension. I read 17.10 and its proof, printed pp.354--355, the paragraph following Definition 17.12, the converse proof of 17.16, printed p.356, and Corollary 17.3, printed p.353. I also read 25.1, p.544, and the preparatory assertion in 25.6(b), pp.545--546, to verify precisely what the parent needs. These support the unchanged item: neither the prescribed torus nor the field must split, and there is no restriction on characteristic or on whether P is proper in G. There are no new nodes to compare to a source. I used no SGA source.

For step 1 I opened lem-sfb-multiplicative-type-largest-subtorus and lem-sfb-solvable-normal-subgroup-products and read their statements. The first expressly says every torus is smooth and connected; the second expressly gives bounded integer dimensions for subgroups and strict increase for any strict inclusion of smooth connected groups. Its dimension clause does not assume those two groups normal or solvable. A greatest attained dimension among tori containing D therefore proves inclusion maximality directly, without a hidden existence or extension theorem. Marking this step elementary is justified by that bounded-integer choice and the one-line contradiction.

For step 2 I read the full statement of lem-sfb-maximal-torus-field-extension: it allows any field extension and smooth connected affine finite-type ambient group, without reductivity or perfectness. Here its ambient group is P, not G; P is closed in affine finite-type G and is smooth and geometrically connected by the item's hypotheses. I read both clauses of lem-pc-proper-base-change: they give properness of X_F and smoothness of P_F and G_F. Connectedness is a hypothesis already stated geometrically. The fppf quotient identification is spelled out on F-algebras and their covering algebras, rather than asserted as an extra uncited base-change theorem. Finite type of X_F follows from properness; affineness and finite type of the groups follow on coordinate rings. No general field has been assumed algebraically closed before F is introduced.

For step 3 I read lem-sfb-borel-conjugation-cover, whose statement explicitly includes Borel existence; no stronger part of that statement is used. The statement of lem-sfb-solvable-proper-fixed-point applies because B is smooth connected solvable and X_F is proper, finite type and has the identity coset. It supplies a fixed point on all algebras, not only on F-points. I opened lem-sfb-homogeneous-orbit-quotient-geometry: it gives both rational lifting and the scheme-theoretic ratio criterion via the displayed fibre-product isomorphism. Those are exactly what produce g and the closed-subgroup containment g^{-1}Bg in P_F. Finally lem-sfb-borel-maximal-torus-conjugacy explicitly says a Borel contains an ambient maximal torus, so it gives S maximal in G_F. The action and conjugation are the natural left multiplication and group-scheme automorphisms; the coset computation is written for every algebra, so no invalid inference from set-theoretic image containment is used.

For step 4 I reopened the conjugacy statement of lem-sfb-borel-maximal-torus-conjugacy. It applies to smooth connected affine finite-type P_F without reductivity; requiring reductivity of P would be incorrect. S is maximal there because it is already maximal in G_F, and T_F is maximal there by step 2. The element p belongs to P_F(F), and conjugating an arbitrary larger R back to a torus containing S proves the exact ambient maximality assertion. Choosing F arbitrarily after T is chosen proves the universal algebraic-closure quantifier with one T, not a different T for each F.

I checked B1--B9: no new statements or proof-bearing unsplit nodes, exact source places, single TeX escapes in parsed JSON, actual logged Mathlib queries, filled existing provenance place and searched same_as. C1--C8 were checked against the eight actual cited statements and verbatim excerpts; the dependency union is exact, all cited nodes are in the item's unit, and the local transitive dependency walk found no path back to this item. D1--D5 are addressed by the actual choice, fixed-point computation and conjugation arguments; no clause has been moved into another node. E1--E7 were checked especially for smoothness of P_F, arbitrary fields and all-algebra equality. The trivial group, D=1, P=G and toral G all fit: bounded dimensions include zero, X is nonempty even when a point, and conjugacy has no positive-rank prerequisite. For a triangular parabolic in GL_2 the chosen torus has rank two, while an anisotropic prescribed D is not incorrectly replaced by a split torus. Finite and imperfect fields are covered solely by the arbitrary-field 17.82 input, so no rational conjugacy over the original field is being assumed.

The proof has step lengths 562, 940, 781 and 705 characters (2988 total); none exceeds 2000 or hides a separate comparison lemma. The server-side review_split check passed before this report was written. The required final deliver.py dry run and delivery follow.

The first dry run required longer excerpts for the torus-smoothness and Borel-existence citations (a 40-character minimum). I replaced those two excerpts by their complete unchanged cited statements; the mathematical proof did not require repair.
