# Stage-1 delivery: lem-sfb-affine-homogeneous-quotient-projective-immersion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-homogeneous-quotient-projective-immersion.json: item, statement, split with six steps; Mathlib searches find no matching theorem. Statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-rational-orbit-arbitrary-field.json: new statement-only lemma; unsplit, no Mathlib match. The general smooth-orbit theorem supplies a locally closed reduced orbit and a faithfully flat locally finitely presented orbit map over any field.
- citations.json: verbatim statement quotations for every step citation.
- searches.jsonl: actual logged searches; report.md: this report. write_split.py is sandbox-only generation code, not a project file.

## Attachments

None. I searched the live WeilConjectures source by the exact blueprint tag, homogeneous quotient, Chevalley, orbit, and line-stabilizer language. No declaration states the item or the new orbit lemma. Project declarations for constructibility, abstract continuous cochains, and linear equations on Lie stabilizers do not establish these algebraic orbit assertions.

## Literature wanted

None. The needed primary source is present: Milne, Algebraic Groups (2017), Theorem 4.27 and Lemma 4.28, pp.94--95; Remark 4.30, p.96; Proposition 1.65 and the orbit paragraph, pp.26--27; Proposition 7.4 and its proof, pp.139--140; Propositions 7.11--7.12, pp.141--142; and Proposition 7.17, Theorem 7.18 and Example 7.19, p.143. I also read Stacks constructions.tex, Tag 01NE (lemma-projective-space), descent.tex, Tag 023Q (lemma-fpqc-universal-effective-epimorphisms), and topologies.tex, Tag 022C (lemma-zariski-etale-smooth-syntomic-fppf-fpqc).

## Corrections and route

The original statement is correct, including arbitrary fields, disconnected smooth G and non-smooth H; no STATEMENT-DISPUTED correction is needed. Its proof was empty. I retained all inherited metadata and the statement. I did not infer that the orbit morphism is smooth from smoothness of G: that would exclude infinitesimal H. The new node explicitly avoids that error.

I read the chapter and unit records and the current latest blueprint's ctf-stability unit and direct-image proof. This item is a supporting algebraic-group input on the inherited alteration/moduli chain, not the unit's key statement. No chapter or unit file is changed. The ancestor command reports a null blueprint root for this inherited item; the new node uses that same null root and prepends the item to the inherited via list. Its place names precisely the orbit input in Milne's proof of Theorem 7.18. Blueprint searches for homogeneous, stabilizer, orbit, orbit map, projective space, 4.27 and 7.4 yielded no blueprint node stating the arbitrary-field orbit lemma or the item. Searches of the whole DAG found the existing Chevalley theorem, which is reused rather than recreated.

## Not duplicates

lem-sfb-smooth-rational-orbit-arbitrary-field vs lem-sfb-smooth-group-orbit-geometry: the existing node assumes k algebraically closed and G connected; this node allows any field and disconnected smooth G. The existing dimension and boundary clauses are unnecessary here and are not copied.

lem-sfb-smooth-rational-orbit-arbitrary-field vs lem-sfb-homogeneous-orbit-quotient-geometry: the existing node likewise assumes an algebraically closed field and connected G, and its conclusion is quotient representability and orbit identification; the new input is local closedness, smooth reduced orbit, and faithful flatness/local finite presentation over an arbitrary field, before any quotient is identified.

lem-sfb-smooth-rational-orbit-arbitrary-field vs lem-sfb-zero-dimensional-stabilizer-finite-orbit: that node assumes an algebraically closed field, connected G and finite stabilizer criteria; the new node has neither algebraic closure nor connectedness nor a dimension-zero stabilizer assumption and does not claim a finite orbit map.

lem-sfb-smooth-rational-orbit-arbitrary-field vs lem-sfb-affine-homogeneous-quotient-projective-immersion: the item asserts existence of a projective immersion for a given homogeneous quotient; the new node starts with an arbitrary action on an arbitrary separated finite-type scheme and proves orbit geometry. It constructs no projective embedding or representation and is not the item's conclusion renamed. The representation, induced projective action, kernel-pair computation and comparison with the supplied quotient remain in the item's proof.

## Review by Q74

I checked sections B--E of delivery-errors against the actual statements and sources. There is exactly one new mathematical input; it is a self-contained statement, with all objects and morphism properties introduced, no proof or proof dependencies, and genuine arbitrary-field content not supplied by the existing orbit statements. Chevalley's scheme-theoretic line theorem is already split in the DAG and is cited, not duplicated. Projective representability, Yoneda, properness of projective space, the covering comparison and morphism descent are existing generic tools; off-unit uses are declared in split_report.tool_uses. No SGA route or citation is used.

For step 1 I read the full statement of lem-sfb-chevalley-scheme-line-stabilizer and Milne 4.27/4.30. It applies to this affine finite-type G and closed H without smoothness or normality of H, and explicitly gives equality on all commutative algebras, not just geometric points. Its nonzero representation ensures N is nonnegative, even for H=G.

For step 2 I read the full projective-space functor statement and Yoneda statement. The former parametrizes invertible quotients with generating sections, so I supplied the duality calculation converting it to locally split sublines of E, rather than misquoting it as a line-moduli theorem. The dual basis gives the generating sections; dualizing a locally split rank-one quotient recovers the inclusion. Both constructions are inverse locally and natural. Applying rho to sublines is then a natural transformation, and the Yoneda bijection supplies the actual action morphism and its identities. The base-change definition of projective space is sufficient because its morphisms are pairs consisting of a structure map to k and the map to projective space over Z. This is a few-line construction from existing representability, not a missing projective-action lemma.

For step 3 I checked that lemma-nagata-projective-space-base-change-proper applies to the finite set of N+1 coordinates and the base Spec k; def-weil-proper-morphism explicitly includes separatedness and finite type. Those are precisely the ambient hypotheses of the new node. For that new node I read Milne's actual Proposition 1.65(c), the orbit paragraph and Proposition 7.4(b), not just Theorem 7.18. Smooth G is geometrically reduced; 1.65(c) and 7.4(b) give the reduced locally closed orbit, factorization and faithful flatness. The proof of 7.4(b) gives smoothness of the orbit without a perfect-field assumption. Local finite presentation follows since the orbit is locally Noetherian, G and the orbit are finite type over k, and a finite-type morphism between these schemes is locally of finite presentation. This latter consequence is part of the new statement to be split later; I did not silently use it as smoothness of the orbit morphism.

For step 4 I read every cited definition and the full Yoneda bijection. The fibre product parametrizes exactly pairs with equal images. Multiplication and inverse give explicit mutually inverse formulas (g,h)->(g,gh) and (g,g')->(g,g^-1 g'). The latter lands in H because H is the full stabilizer from step 1. The open/closed immersion definitions give test-scheme monicity locally from open inclusions and surjective ring maps. Thus the argument verifies the actual kernel pairs, including nilpotent test algebras; it never replaces the stabilizer by its reduction. The other kernel-pair isomorphism is a hypothesis of the item itself.

For step 5 I checked the precise statements of def-pc-fppf-site, lem-trf-fppf-covering-is-fpqc and lem-weil-pbc-fpqc-representable-descent. Flatness, local finite presentation and surjectivity hold for q by assumption and beta by step 3, so both singleton families meet the fppf definition. The covering comparison gives actual fpqc covers. The morphism-descent theorem has the full existence and uniqueness clause required for u and v. The step checks compatibility using the two computed kernel pairs, and then uses uniqueness to prove the two inverse identities and the k-structure identities. It does not cite a mere fully faithful Yoneda theorem for descent.

For step 6 I checked the closed-immersion definition: transporting the closed inclusion O->U by the isomorphism Y~O preserves the closed underlying image and the surjection on structure sheaves. This directly gives the demanded closed-into-open factorization. No unproved general composition theorem is invoked.

Small cases: H=G (including G=1) gives a fixed rational line and a one-point orbit; N=0 is allowed. For G_m acting on G_m by (g,z)->g^p z in characteristic p, H=mu_p is nonreduced and the orbit map is Frobenius, faithfully flat but not smooth; the new node and the kernel-pair/descent argument remain valid. For a constant group with two elements acting on itself over any field, the orbit is disconnected, checking why connectedness cannot be borrowed from the existing nodes. For a trivial action on a nonreduced finite-type ambient scheme the orbit at a rational point is its reduced rational-point subscheme, not the whole infinitesimal thickening. Nothing requires perfection or algebraic closure. I checked that neither cited node depends on the item or the new orbit lemma, and every new proof step is below 2000 characters.

Mathlib searches were executed with msearch.py and their returned hits read. For the item I tried both quotient-embedding and homogeneous-space phrasings; the hits are abstract group/topological quotients, Proj, quasi-affine schemes, Grassmannian projective quotient modules or elliptic curve coordinate conversions, not homogeneous-space projective embeddings. For the new node I tried two orbit phrasings, Loogle's orbit/flat query, and a grep of AlgebraicGeometry. Hits give smoothness definitions, flatness criteria and the locally closed range of an already-known immersion, not construction or faithful flatness of algebraic group orbits. There are no Mathlib leaves. All citations.json quotations are copied verbatim from the cited statements.

## Unfinished work

The item is split. The single new general orbit lemma is intentionally statement-only for a later stage-1 worker. No Lean was written or compiled; no repository or launcher file was edited.
