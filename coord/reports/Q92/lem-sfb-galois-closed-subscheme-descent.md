# Q92 stage-1 report: lem-sfb-galois-closed-subscheme-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-galois-closed-subscheme-descent.json — statement, now split; statement unchanged; no Mathlib match for the whole item.
- citations.json — 24 entries, one for every step/node pair, copied verbatim from the cited node statements.
- report.md — this report. searches.jsonl is the unmodified log produced by msearch.py.

No new nodes; no new Mathlib leaves. Only the sandbox has been written.

## Attachments

None. Searching WeilConjectures for the exact blueprint tag and for Galois descent of closed subschemes found no declaration covering this item. AlgebraicGeometry.exists_closed_subset_of_galois_invariant in AlgebraicGeometry/GaloisInvariantClosedSubsetDescends.lean:51 descends a closed subset, not its defining ideal; it cannot be attached here. The matrix descent results concern fixed matrix spaces, not arbitrary defining ideals. The ideal extension declaration Scheme.IdealSheafData.ideal_comap_appLE is already carried by lem-pc-ideal-sheaf-comap-affine-extension, which is reused.

## Wanted literature

None.

## Findings and changes

The original item was unsplit with no proof. Its statement agrees with Milne A.65 and is unchanged. The subgroup deduction requires a scheme-theoretic, rather than a geometric-point, argument. Milne A.66's graph argument explicitly assumes a separated target, an assumption absent from this item; the proof therefore uses the affine ideal-vanishing argument behind A.65 to reflect point membership, then tests the subgroup condition on every commutative base algebra. This imposes no new separatedness hypothesis.

The shared DAG acquired lem-sfb-galois-stable-subspace-descent (Q122) during this session. I read its complete statement and reused it rather than create a finite-Galois duplicate. It permits arbitrary-dimensional vector spaces and possibly infinite algebraic normal separable extensions, so it applies to each coordinate algebra A and its E-linear ideal J with exactly the hypotheses available here. The existing lem-sfb-galois-descent-affine-subgroups is limited to affine ambient group schemes; it does not replace the nonaffine closed-subscheme argument needed here.

I retained the existing blueprint provenance. blueprint_refs.py ancestor reports None: the recorded created.item chain ends in an audit seed, so I have not invented an imported ancestor. I read the newest blueprint via literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, particularly clause (3). The inherited provenance describes the alteration prerequisite chain below that clause; this split addresses its auxiliary closed-subscheme descent input, without changing any unit or chapter.

## Searches and not duplicates

I searched the entire DAG by titles, statements, Galois descent, closed subschemes, invariant subspaces, A.64 and Tag 0CDR, as well as the blueprint_refs.py searches for Galois descent, closed subscheme, semilinear, vector space, invariant subspace, Galois stable linear, and semilinear vector. There are no new node/existing node pairs to distinguish. The useful existing statements were opened in full before citation. In particular the infinite-extension subspace descent lemma is strictly more general than the proposed finite-extension auxiliary, and is used directly.

The item retains its previous searches and appends only the searches actually run through msearch.py in this sandbox. Both natural-language services and Loogle were available. The first and second subspace phrasings returned fixed-field invariants, prime-ideal transitivity and scalar-extension submodule descriptions; they do not prove invariant-subspace descent. The closed-subscheme phrasings returned integral-closure invariants and field Galois connections, not descent of defining ideals. The grep of AlgebraicGeometry/IdealSheaf finds order-theoretic Galois connections; grep in FieldTheory finds purely inseparable semilinear Frobenius. The whole-Mathlib grep finds ordinary invariant subspaces of endomorphisms. None supplies the item. I read the project closed-subset declaration, the matrix-span implementation, the affine ideal-comap implementation, and the invariant-ring source to distinguish those results.

## Review by Q92

I read Milne iAG2017 Appendix A.64–A.66, printed pp.580–581 (PDF pp.592–593). A.64 explicitly permits infinite-dimensional spaces; A.65 states uniqueness for arbitrary field extension and existence under scheme-theoretic Galois invariance, first by ideal descent on affines. I checked the supplemental Stacks sources: descent.tex Tag 0CDR (lemma-galois-descent) and its explicit cocycle discussion, schemes.tex Tag 01IN (lemma-closed-subspace-scheme), and morphisms.tex Tag 01QQ (lemma-closed-immersion-bijection-ideals). The defining ideals remain the original ideals throughout; no radical or reduced replacement is made. No new node needs a source review. No SGA source is used.

Step 1 uses the actual open-fibre-product and affine-spectrum tensor-product statements to identify U_E, the ideal-sheaf statement to obtain J_U, and the general stable-subspace statement to write J_U as the E-span of I_U. These are precisely their stated conclusions. The extension is finite Galois, hence algebraic normal separable as the subspace result requires. No finite dimension of the coordinate algebra or of its ideal is assumed. The equality of the E-span with the extended ideal is proved explicitly by multiplying pure tensors; it is not silently taken from a descent definition.

Step 2 uses the principal-open clause (0) of lem-weil-pbc-affine-ideals-closed-subscheme, the localization-over-the-base tensor isomorphism with R=k, A=the chart ring, M=A, N=E and T the powers of f, and the affine ideal-comap formula for open restriction on X_E. The latter allows precisely an affine source contained in the inverse image of an affine target. The field-extension base-change lemma gives faithful flatness for A_f, and the ideal-contraction lemma then contracts the extended ideal. Together they prove I_(U_f)=I_U A_f; no arbitrary affine intersection is treated as affine. I verified that none of these nodes only defines the property being used.

Step 3 uses exactly the compatibility proved in Step 2 as the hypothesis of the affine-ideal construction lemma, obtaining the closed immersion with those ideals. The affine-comap statement computes the ideals of its base change; Step 1 gives equality with J_U on an open cover. The kernel ideal-sheaf statement supplies the quotient descriptions, so the equality is of closed subschemes and their embeddings, not merely their underlying sets.

Step 4 is the explicit contraction calculation for any other candidate ideal I'_U. The cited field-extension and ideal-contraction statements apply to every commutative chart algebra, with no reducedness or finite-type requirement on that algebra. The quotient descriptions of a closed immersion then give uniqueness up to the unique ambient-compatible isomorphism, the ordinary meaning of uniqueness of a closed subscheme.

Step 5 checks the only extra ingredient needed for subgroup descent: membership of an R-point can be tested after R→R tensor_k E. On each affine V inside the inverse image of an affine target, ideal-comap identifies the extended defining equations and the field-extension/contraction statements give injectivity of B→B tensor_k E. Thus each equation vanishes on V and hence on the whole inverse image by the sheaf axiom. The cited closed-immersion lift lemma explicitly supplies a factorization when these maps on every affine target annihilate the defining ideal, exactly what has just been shown. This is a few-line application of the existing statements, not a new general factorization lemma or a use of A.66 outside its hypotheses.

Step 6 uses the actual group and closed-subgroup definitions: test every commutative k-algebra R, including nonreduced R, pass its points to the E-algebra R tensor_k E, then use Step 5 on the identity, products and inverses. The base-change universal property identifies these algebra-valued points and respects the operations. Injectivity of Z(R)→X(R) is written out using the quotient surjections on affine charts. This proves the definition directly; no unrecorded representability or descent-of-morphisms theorem is invoked.

I checked delivery-errors B–E against the files. B: there are no new nodes; the original complete statement, TeX, provenance and metadata are retained, every appended search was actually run, and no Mathlib leaf is asserted without a match. C: every uses entry has a verbatim citation; the statements supply the exact clauses above; no source proof is substituted for a node statement. The only nonclosed off-unit tool is the affine ideal-comap lemma and is declared in split_report.tool_uses. D: the argument remains in this item's six steps and uses existing smaller results; it does not move a clause to a new node. E: I checked the empty scheme, Z_E empty, Z_E=X_E, E=k, nonradical ideals such as (t^2), characteristic dividing the Galois group order, and nonseparated finite-type X. The proof uses no averaging or division by the group order, no reducedness, and no separatedness. A proper empty closed subscheme of a nonempty group cannot satisfy the subgroup hypothesis (it lacks the identity), consistently with Step 6. All steps are below 2000 characters, and the factorization and compatibility calculations are written out.

## Unfinished work

None within the authorized stage-1 split. The reused unsplit stable-subspace lemma remains its own existing DAG item; this delivery does not claim a Lean proof. No Lean was written and no compiler, Lake or build command was run.
