# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-rank-one-adjoint-projective-linear.json: item split into six steps, statement unchanged, existing searches and provenance retained.
- lem-sfb-rank-one-flag-curve: statement, not in Mathlib; dimension-one Borel quotient.
- lem-sfb-rank-one-opposite-borel-intersection: statement, not in Mathlib; two Borels and their full scheme intersection.
- lem-sfb-complete-curve-connected-linear-action: statement, not in Mathlib; general homogeneous-curve input.
- lem-sfb-pgl2-proper-connected-subgroup-solvable: statement, not in Mathlib; proper reduced connected PGL2 subgroups.
- citations.json: 26 entries, each checked against the exact statement of the cited node.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint id, PGL/pgl, semisimple/reductive, rank-one, Borel curve, homogeneous curve and opposite Borel. There is no declaration giving this theorem. In particular the upstream abstract matrix-group results do not give an affine group-scheme assertion.

## WANTED

None. All mathematical sources used are available locally in literature/.

## Corrections and scope

The item was statement-only. Its statement agrees with Milne 20.22 and is unchanged. Its semisimple-rank hypothesis uses G/R(G), not the total torus rank of G. The current blueprint direct-images proof paragraph (3), its unit and chapter, and the inherited chain to the rank-one classification were read. This supplies an input below that chain; it changes no unit or chapter route and is not the key node of the unit. The inherited blueprint ancestor is null: blueprint_refs.py ancestor prints None. New nodes preserve that exact ancestry and extend the inherited place/via; this existing metadata fault is not silently assigned a different ancestor.

The reverse centre inclusion is written using Z(G) contained in a maximal torus and the coset action. This avoids using the unproved assertion that the centre of PGL2 is trivial. The proof of Milne 20.16 speaks of proper subgroups being solvable; here the image is explicitly proved reduced and connected before applying that fact, because disconnected finite subgroups need not be solvable. No claim is made for nonreduced proper subgroup schemes. Nothing was left unfinished. No Lean was written or compiled, no repository or launcher file was changed, and no git command was run by the worker.

## Not duplicates

lem-sfb-rank-one-flag-curve vs lem-sfb-general-borel-flag-variety: the latter supplies the flag scheme and action but gives no dimension-one conclusion from semisimple rank one.

lem-sfb-rank-one-flag-curve vs lem-sfb-borel-quotient-affine-cell: an affine-space cell of unspecified dimension does not prove the quotient has dimension one.

lem-sfb-rank-one-opposite-borel-intersection vs lem-sfb-unipotent-root-intersection-products: the latter assumes the full root subgroups and positive-root Borel data of reductive-borel-pair-structure. The new statement uses only reductivity and semisimple rank one, supplies exactly two Borels, and precedes the root-datum construction. That existing root-data branch depends on the item, so using it here would be circular. Milne 20.18 proves the scheme intersection before general root theory.

lem-sfb-rank-one-opposite-borel-intersection vs lem-sfb-chevalley-borel-intersection: the latter gives only the reduced identity component of the intersection of all Borels through a torus. It does not identify the full scheme intersection or exclude an infinitesimal part.

lem-sfb-rank-one-opposite-borel-intersection vs lem-sfb-double-flag-invariant-boundary: the latter assumes a semisimple simply connected group and rho/root Borel data; it neither asserts exactly two Borels nor applies to general reductive rank-one groups without those later data.

lem-sfb-complete-curve-connected-linear-action vs lem-sfb-projective-frames-pgl: projective-frames-pgl describes automorphisms once the curve is already projective space; it does not classify the curve.

lem-sfb-pgl2-proper-connected-subgroup-solvable vs lem-sfb-solvable-proper-fixed-point: fixed-point existence requires solvability as a hypothesis; it does not supply it for a subgroup of PGL2.

All four new nodes vs lem-sfb-rank-one-adjoint-projective-linear: none states the adjoint quotient or a kernel equality. Their statements are smaller geometric/structural inputs; the item constructs q, proves its faithful flatness, proves both kernel inclusions and constructs the quotient isomorphism in its own steps. Whole-DAG statement/source searches and blueprint_refs searches for rank one, projective line, homogeneous, Borel, 20.16, 20.5, 17.27 and 20.21 found no blueprint counterpart. Keyword PGL searches found matrix and invariant-theory nodes, not these statements.

## Review by N0

I read Milne iAG2017 printed pp.408--415: Proposition 20.5 for the complete-curve action node; 20.16 (a) implies (c) for flag dimension; 20.16 (a) implies (b), 20.18 and 20.21 for the full opposite-Borel intersection; and the proof of 20.22 for assembly. I also read printed p.360, Corollary 17.27, used in 20.16 (c) implies (d), for proper connected PGL2 subgroup solvability. The new node includes reducedness and connectedness: over algebraically closed F the reduced connected subgroup is smooth, and a proper subgroup of the smooth integral three-dimensional PGL2 has dimension at most two. It is intentionally not the false claim for arbitrary finite/disconnected subgroup schemes.

Step 1 uses general-borel-flag-variety to obtain a Borel, borel-maximal-torus-conjugacy to obtain a maximal torus in it, and the new opposite-intersection node to choose the second Borel. I opened both quotient statements: homogeneous-orbit-quotient-geometry gives the represented fppf cosets and F-point lifting; algebraic-group-homogeneous-quotient supplies finite presentation as well as flatness/surjectivity, which borel-quotient-proper-geometry requires. The latter gives smoothness, integrality and properness, not dimension one: the new flag-curve statement supplies dimension one. All group and Borel smooth/connected hypotheses hold by reductivity and the definition of a Borel.

Step 2 writes the coset action explicitly, rather than assuming a definition node proves the action. Associativity makes it well defined and the sheaf quotient extends it naturally; its unit and multiplication identities are the group identities. Transitivity on F-points comes from the exact statement of the homogeneous quotient. Its orbit map is the quotient map, so the action is nontrivial because the quotient has positive dimension. The complete-curve node applies with H=G and the smooth proper integral curve from step 1. Projective-frames-pgl states the automorphism SHEAF is PGL, naturally under all base change, so it gives the group-scheme homomorphism, not merely an abstract map on F-points.

Step 3 uses affine-homomorphism-flat-image for a faithfully flat map to a CLOSED image I. I checked the ring injectivity statement with N=F[I]. Smooth-geometrically-reduced applies to the structure morphism G over F, so F[G] is reduced; its subring F[I] is therefore reduced. The faithfully-flat spectrum lemma supplies actual surjectivity, making I a connected continuous image of G. The new proper-subgroup lemma is now applicable, with precisely its reduced and connected hypotheses. The fixed-point node states a point fixed after every algebra extension, so it applies to the whole group action. Such a point is inconsistent with the transitive G(F) action on a projective line with distinct 0 and infinity. This proves I=PGL2 and hence faithful flatness, without assuming separability of q or smoothness of its kernel.

Step 4 reads the quotient kernel-pair equality to identify the stabilizer of eB with B on all test algebras. The normalizer-transitivity statement gives n conjugating the two Borels, and normality of the kernel puts K in both. The new intersection node is scheme-theoretic, not only its reduction. The split-torus-subgroups statement identifies this K with Spec F[M] even when K is nonreduced. The connected-action-multiplicative-type-rigidity statement allows precisely such a nonreduced K and says conjugation is trivial. Thus K is contained in the full functorial centre.

Step 5 uses affine-group-centre-base-change for representability. I opened reductive-torus-self-centralizer: it says C_G(T)=T on all test rings and requires a geometrically maximal torus; over algebraically closed F our T meets that condition. Hence Z(G) is in B. For an arbitrary point of the quotient, the represented fppf coset sheaf supplies a local lift; zgB=gzB=gB proves the action is the identity locally and then by the sheaf condition globally. This proves the reverse kernel inclusion without discarding infinitesimal central elements.

Step 6 applies the faithfully-flat-group-quotient-universal statement twice with the two faithfully flat arrows p and q and the already PROVED identical kernels. Its uniqueness gives both inverse identities. Normal quotient geometry supplies p and its kernel. There is no unstated isomorphism criterion or appeal to field-valued injectivity.

For small cases I checked G=SL2 (kernel mu2), PGL2 (trivial kernel), GL2 (central G_m), and each product with a torus. Characteristic two retains mu2 as a scheme and no argument divides by two; the opposite-Borel node expressly includes nonreduced algebras. A rank-zero torus or the trivial group does not satisfy the semisimple-rank-one hypothesis, so cannot be fed into the flag-curve lemma. The curve node excludes a trivial action, a zero-dimensional scheme and a non-affine acting group (elliptic translations would otherwise be a counterexample). The subgroup node includes the trivial, additive, torus and Borel subgroups and deliberately excludes disconnected nonsolvable finite subgroups. A proper nonreduced Frobenius-preimage subgroup is outside its hypothesis; reducedness of our I was proved first.

I checked B1--B10: every new node is statement-only, introduces all its objects, cites every definition (including grouped bracket citations), keeps single TeX escapes, supplies exact Milne theorem/page references rather than invented Stacks tags, carries ancestry and actual logged searches, and has no claimed Mathlib match. All leanfinder/leansearch hits were read: abstract matrix groups, Lie-algebra root systems and solvability, order-theoretic flags and Weierstrass coordinate formulas do not state these group-scheme results. Loogle's unknown identifier AlgebraicGeometry was recorded literally and was supplemented by the valid Borel substring search; it is not evidence of mathematical absence. There are at least two semantic phrasings for each mathematical search question (LeanFinder and LeanSearch), plus Loogle and grep. Existing Lean sorry declarations were never treated as attachments. All citation quotes are verbatim statement substrings. No proof step exceeds 2000 characters; no SGA source or route replacement is used. The main repairs during this audit were adding the explicit reduced/connected-image check, providing finite presentation before applying the quotient geometry node, and expanding grouped definition citations in stmt_deps. The report records the inherited null ancestor rather than concealing it.
