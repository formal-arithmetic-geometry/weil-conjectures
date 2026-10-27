# Stage-1 worker report

Item: lem-sfb-maximal-torus-field-extension. Group: NU. Date: 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-maximal-torus-field-extension.json: statement, now split; statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-torus-free-implies-unipotent-arbitrary-field.json: new statement-only unsplit node; no Mathlib match. This is Milne 17.81 over arbitrary fields, not just algebraically closed fields.
- dag/nodes/sec-six-functors-basics/lem-sfb-central-extension-of-tori.json: new statement-only unsplit node; no Mathlib match. This supplies the inverse-image argument using Milne 16.43.
- citations.json: 17 exact quotations, covering every citation of the item's six steps.
- report.md: this report. searches.jsonl contains the actual msearch output records; write_split.py is sandbox-only preparation, not a delivery file.

## Attachments

None. Searches in lean/WeilConjectures for the blueprint tag, maximal torus, MaximalTorus, torus, and the relevant group-theoretic terminology found no declaration stating this item or either new input. The torus occurrence in TraceBound.lean concerns compact topological tori; DerivedOpenDifferenceDiagram.lean concerns unipotent biproduct matrices.

## WANTED

None. All sources used are present locally. No SGA source is used.

## Problems found and corrections

The item's statement agrees with Milne Theorem 17.82, printed p.379, restricted as requested to smooth connected affine groups. No STATEMENT-DISPUTED issue arose and no statement hypothesis or conclusion was changed.

The existing lem-sfb-no-torus-unipotent assumes an algebraically closed base. Applying it directly to C_G(T)/T over an arbitrary field would be invalid: absence of base-field tori cannot be silently replaced by absence of geometric tori. The new arbitrary-field node supplies exactly the input 17.81 used by Milne. The other needed fact is that the inverse image of a quotient torus is itself a torus when its kernel is central and a torus. The proof now exposes that input rather than calling the inverse image a torus without justification.

I retained the inherited blueprint ancestry: blueprint_refs.py ancestor returns None, and the existing from.node is null. The new nodes extend the inherited via chain and give the precise Milne proof sentence served. I read the latest blueprint's sk-thm-sf-ctf-stability unit and its direct-images proof (3), as well as the chapter and unit DAG records. The inherited long alteration/moduli/representation prerequisite chain remains supporting material; no chapter or unit route is replaced. The current blueprint has no node stating this auxiliary group theorem. The item is not the key node of the unit, so no unit file is written.

While checking source locations I corrected my draft citation of 17.99: it is Proposition 17.99 on printed pp.383–384, not a theorem on p.386. I also removed two unused statement dependencies from the new central-extension node. The final source citations use the actual labels and printed pages, and the Stacks input is identified by Tag 04KV and its label, not by a moving section number.

## Unfinished work

The item has a complete one-level split. Both new nodes intentionally have statements only and remain unsplit for future workers. Their proofs have not been claimed as finished. No Lean was written and no compiler, Lake or build command was run.

## Not duplicates

lem-sfb-torus-free-implies-unipotent-arbitrary-field vs lem-sfb-no-torus-unipotent: the existing node is restricted to algebraically closed fields; the new node allows arbitrary fields and tests torus subgroups defined over that field. The new result requires Milne's additional arbitrary-field argument, including its finite-field case.

lem-sfb-torus-free-implies-unipotent-arbitrary-field vs lem-sfb-geometric-unipotence-unitriangular-embedding: the existing node assumes a faithful representation with all geometric points unipotent. The new node deduces unipotence from absence of base-field tori; it does not assume geometric unipotence.

lem-sfb-central-extension-of-tori vs lem-sfb-commutative-multiplicative-type-extension: the existing node assumes the middle group commutative and works over an algebraically closed field; the new node does not assume it commutative and works over any field, using connectedness and the central torus kernel. Commutativity is part of the content of Milne 16.43 and cannot be assumed in the inverse image.

lem-sfb-central-extension-of-tori vs lem-sfb-affine-normal-quotient-geometry: the existing node constructs quotient geometry and proves smoothness and connectedness of inverse images; it does not assert that an inverse image with torus kernel and quotient is a torus.

Neither new node mentions maximality or extension of the ground field as its conclusion. Neither restates the item or one of its two directions. Searches of the whole DAG by maximal-torus, central-extension, no-nontrivial-torus, multiplicative-type, and the Milne references found no existing node with either statement. Whole-blueprint searches with blueprint_refs.py for maximal torus, torus, unipotent, centralizer, multiplicative type, connected group, central extension and nontrivial torus likewise found no replacement. The returned analytic tori, abstract torsion groups, Lie algebra Cartan results and ring-flatness declarations do not concern algebraic group schemes. Each new node has its own semantic query, a second phrasing, Loogle query and logged grep; none is marked Mathlib.

## Review by NU

I read Milne, Algebraic Groups (2017), Theorem 17.82 on p.379 and its proof, Proposition 17.81 on pp.378–379, Lemma 16.43 on p.340, Corollary 14.9 on p.282, the unipotence criterion Theorem 14.5 on pp.281–282, and the discussion of multiplicative type and tori around Theorem 12.23 on p.240. I also read 17.72 on p.376, the centralizer base-change paragraph after Proposition 1.92 on p.34, and Proposition 17.99 and its proof on pp.383–384 to check the finite-field reference. For the scheme connectedness tool I read literature/stacks-project/varieties.tex, lemma-geometrically-connected-if-connected-and-point, Tag 04KV. These sources support the unchanged item and both new statements with precisely their field and smoothness hypotheses.

For step 1, I opened lem-sbc-connected-rational-point-geometrically-connected: its statement explicitly gives connectedness after every field extension from a connected scheme with a section. G has its identity section. I opened lem-pc-proper-base-change and use only clause (2), smoothness after base change. Its properness clause is unused. The cited finite-type and torus definitions support the written coordinate-generator and splitting arguments; no assumption that k is perfect is introduced. These off-unit scheme facts are declared as generic tool uses in split_report, not as changes to the unit's proof route.

The final self-review also checked the smoothness and connectedness of the tori needed in step 3. I opened lem-pc-scheme-connected-iff-idempotents and lem-sfb-geometrically-reduced-group-smooth; their statements give exactly connectedness from trivial idempotents and smoothness from geometric reducedness for locally finite-type groups. Step 1 now verifies their hypotheses by injecting each extended coordinate algebra into the splitting Laurent ring, whose domain property is proved by its leading monomial. The identity point verifies nonemptiness. I read Milne Proposition 1.26(b), p.13, and the subsequent idempotent discussion, pp.14–15, for this check. This addition makes the use of torus smooth connectedness explicit and introduces no new node.

For step 2, I read the full statements of lem-sfb-torus-centralizer-smooth-connected and lem-sfb-affine-normal-quotient-geometry. The first requires geometric connectedness, provided by step 1, and gives a smooth geometrically connected closed centralizer for any torus, without requiring maximality or reductivity. Affineness and finite type follow from its stated ambient conventions. The second gives the quotient, kernel, faithful flatness, finite presentation and smooth connected quotient. T is central in C on all algebras by the centralizer definition. The comparison of maximality in G and C is written out using commutativity of any containing torus.

For step 3, the quotient node explicitly gives the inverse image P, its smooth connectedness when both kernel T and subgroup R are smooth connected, and P/T isomorphic to R. Thus every hypothesis of the new central-extension node is checked: P is affine finite type, smooth connected, its kernel T is a torus central in P, and its quotient R is a torus. Maximality forces P=T and hence R=1. This is an actual inverse-image argument rather than a citation of the desired conclusion.

For step 4, I read the new arbitrary-field node as a standalone statement. It requires exactly a smooth connected affine finite-type Q with no nontrivial torus defined over its field. Steps 2 and 3 supply these hypotheses. I did not cite the algebraically closed version as if it had this statement.

For step 5, I opened lem-sfb-unipotent-to-multiplicative-trivial and take only its unipotence definition and field-invariance clause, not its homomorphism-vanishing direction (which goes the other way). I opened lem-sfb-diagonalizable-group-geometric-criteria, which identifies D(Z^r) with the split torus, and lem-sfb-diagonalizable-to-unipotent-trivial, which gives vanishing on all algebras, even nonreduced ones. These statements apply to S over the algebraic closure and the unitriangular embedding of Q there. I explicitly descend equality of coordinate maps using injectivity of scalar extension of vector spaces. I then use the already constructed scheme-theoretic kernel, not merely geometric points of T, to obtain S contained in T. This repairs the potential C4 direction error and E3 pointwise-factorization error.

For step 6, I checked the fibre-product definition gives the claimed functor of L-algebras. Its centralizer tests agree because an algebra extension of an L-algebra already acquires the required L-structure. The quotient node's statement explicitly includes compatibility with every field extension. The unipotence node explicitly says unipotence is both preserved and tested by any field extension. Thus the criterion already proved can be applied on each side; there is no unproved assertion that maximality itself is geometric.

Small cases checked: G=1 and rank-zero T give Q=1 and both maximalities. For G=G_a, T=1, Q is unipotent and maximality persists even in positive characteristic. For G=G_m and T=1, Q=G_m has a nontrivial torus and is not unipotent, so both sides correctly fail; T=G makes Q=1. An anisotropic real torus is itself a nontrivial torus even though it has no nontrivial split subtorus over R: the new arbitrary-field node concerns all tori, not only split ones. Over finite fields the new node invokes the separate 17.99 argument, not the infinite-field Lie-algebra argument. For the central-extension node, T=1 or S=1 reduces to a torus immediately, while E=G_m^a times G_m^b verifies the nonzero-rank case. Finite infinitesimal multiplicative groups such as mu_p cannot be substituted for a torus in either hypothesis; all-algebra vanishing in step 5 avoids treating their geometric point set as a group-scheme equality.

I checked B–E against the final files: new nodes are self-contained and statement-only, with no proof hidden in their statements; all named notions have definition citations or explicit meanings; TeX has ordinary single backslashes after JSON decoding; the dependency lists contain no missing or merged node. The existing citations were checked for a path back to the item and none has one. The two new lemmas are independent supporting assertions, not a relabelling of either field-extension implication. Every proof citation has an exact statement quote in citations.json. No step exceeds 2000 characters (the longest is 1543), so there is no long step concealing an omitted lemma. The item's existing source, metadata and statement are preserved. The first required dry run passed. After it, the final self-review made the torus smoothness/connectedness verification explicit; the required dry run is repeated for those final files before pushing.
