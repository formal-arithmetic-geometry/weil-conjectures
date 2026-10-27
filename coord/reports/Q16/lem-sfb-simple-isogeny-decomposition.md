# Stage-1 delivery: lem-sfb-simple-isogeny-decomposition

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-simple-isogeny-decomposition.json: item split into eleven steps; statement and statement dependencies unchanged; retained the earlier Q41 research and provenance.
- lem-sfb-abelian-inclusion-multiple-retraction: statement-only; no Mathlib match. An abelian inclusion has a retraction up to positive multiplication.
- lem-sfb-abelian-hom-image-dimension: statement-only; no Mathlib match. Image abelian variety and dimension formula for arbitrary-field abelian homomorphisms.
- lem-sfb-abelian-kernel-abelian-part: statement-only; no Mathlib match. A kernel contains a ground-field abelian subvariety of the same dimension, plus the zero-dimensional finite conclusion.
- lem-sfb-finite-group-scheme-order-annihilator: statement-only; no Mathlib match. Scheme-theoretic annihilation by rank, including nonreduced finite group schemes.
- lem-sfb-abelian-finite-product: statement-only; no Mathlib match. Finite products, dimensions, empty product, and zero-dimensional abelian varieties.
- citations.json: 36 verbatim statement quotations, one for every step/citation pair.
- searches.jsonl: actual outputs recorded by the prescribed search script. Local helper scripts only generate the sandbox JSON and this report.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and for simple abelian varieties, isogenies, quasi-inverses, Poincare reducibility and Rosenlicht. Read AbelianVariety/Basic.lean, Isogeny.lean and GroupScheme/Image.lean. Existing project declarations prove multiplication isogenies, finiteness/flatness of an isogeny, and the closed-subgroup image, but do not prove all the item's clauses or any new prerequisite exactly. Existing closed project results are reused through their existing nodes.

## Wanted literature

None needed to state this one-level split. The documents used are present. Milne AV's footnotes explicitly leave arbitrary-field geometric reduction checks unfinished; that gap is exposed as an unsplit prerequisite, not treated as a proved fact.

## Corrections and route

The item itself is true as stated, including over imperfect fields; no statement dispute or weakening was made. Milne AV I Proposition 10.1 (p.42, footnote 10) uses a kernel component whose geometric reducedness is left unproved over imperfect fields. The paragraph on p.43 repeats the problem (footnote 11). The DAG's existing lem-sfb-abelian-closed-subgroup-reduced-component assumes an algebraically closed field and cannot be used with this item's arbitrary k. The existing polarization-calculus node likewise assumes algebraic closedness. Neither is cited.

For the complement argument I use the positive multiple retraction of Milne iAG Proposition 8.23, normalize it as in Theorem 8.24, and form C=Im([n]-ir). Smooth-source images are geometrically reduced by iAG Theorem 1.72, so C is an abelian variety over the original field. The kernel abelian-part input needed for simple maps is isolated separately with exactly the arbitrary-field assertion that the source's footnote says still needs proof. It is not the simple-map conclusion or the decomposition clause. This is a choice below the unit route, in the auxiliary abelian-Hom finite-freeness branch of constructible direct-image stability. No unit or chapter was changed. The nearest blueprint ancestor command returns None; the inherited from.node=null and via list are retained and extended exactly as prescribed by that output.

## Mathlib and duplicate searches

Before creating the five nodes I searched the entire DAG by the mathematical statements, tags and source places, and searched the whole imported blueprint with blueprint_refs.py for isogen, Poincare reducibility, simple abelian, abelian subvariety, retraction, finite group scheme, reduced identity, homomorphism theorem, product of abelian, dimension of the product, multiple retraction, and 0B2M. I read the current blueprint unit under literature/blueprint/latest/. The item is auxiliary to the unit, so it does not fill its realized fields.

For the item and each new node, the prescribed msearch.py ran LeanFinder, Loogle, grep and LeanSearch, with a second mathematical phrasing. Every recorded query matches searches.jsonl verbatim. Schur.isIso_of_hom_simple (Mathlib/CategoryTheory/Preadditive/Schur.lean:45, read) assumes simple objects and kernels in an already supplied preadditive category; geometric k-simplicity is not that predicate in the category of abelian varieties. The up-to-isogeny category and its kernel theory would themselves require the present mathematics. The finite-group hits concern cardinalities of abstract groups, not the coordinate-algebra rank, so do not apply to infinitesimal group schemes. Mathlib smooth_of_grpObj (Group/Smooth.lean:64, read) assumes geometric reducedness, which is part of what the image lemma must establish. The product queries returned module/Lie-group products and smooth relative dimension composition, not this package for abelian varieties. No new Mathlib leaf is claimed.

## Not duplicates

lem-sfb-abelian-finite-product vs thm-pd-fpqc-local-properties: the new node states finite products of abelian varieties, dimension additivity and the zero-dimensional identity case; the existing node states Properties of morphisms are local in the fpqc topology on the target, not this product/zero-object package. Shared background tag(s): 0BFC.
lem-sfb-abelian-finite-product vs lem-sc-abelian-variety-characterization: the new node states finite products of abelian varieties, dimension additivity and the zero-dimensional identity case; the existing node states Abelian varieties are the complete group varieties, not this product/zero-object package. Shared background tag(s): 03RO, 0B7Q, 0BFC.

lem-sfb-abelian-hom-image-dimension vs lem-sc-image-subgroup: the latter only states that the image is a closed subgroup and the source-to-image map is surjective; it does not state smoothness, geometric reducedness, connectedness or the dimension formula. The new node explicitly cites it as a statement dependency.
lem-sfb-abelian-kernel-abelian-part vs lem-sfb-abelian-closed-subgroup-reduced-component: the existing statement assumes algebraic closedness and constructs the reduced identity component for any closed subgroup; the new statement is restricted to homomorphism kernels but works over every ground field and does not assert that reduction is smooth over an imperfect field.
lem-sfb-abelian-inclusion-multiple-retraction vs lem-sfb-abelian-polarization-calculus: the latter defines the dual/polarization maps over an algebraically closed field and gives no retraction of an arbitrary inclusion over its ground field.
lem-sfb-finite-group-scheme-order-annihilator vs lem-sc-connected-finite-order: the existing statement only identifies the rank as a p-power for connected finite groups in characteristic p; it does not say rank kills every R-point, including the non-etale scheme structure.
lem-sfb-finite-group-scheme-order-annihilator vs lem-sfb-abelian-torsion-kernel-divisibility: that node is a prime-to-characteristic, algebraically closed factorization result; it does not annihilate arbitrary finite subgroup schemes. It is not used to justify the inseparable case here.

## Review by Q16

I read Milne AV I Proposition 7.1 (p.32), Remark 8.6 (p.36), Proposition 10.1 (p.42) and the discussion after Remark 10.2 (p.43), including both imperfect-field footnotes. For the new retraction node I read iAG Lemma 8.22, Proposition 8.23 and the proof of Theorem 8.24 (pp.152–153): the integer is a positive separable degree in Lemma 8.22, and translating the value at the identity makes the map a homomorphism by 8.19. The image node follows iAG Theorem 1.72 (pp.28–29) and Remark 5.42 (pp.108–109); the source is smooth, proper and connected, so the claimed image has the required properties, unlike a general nonsmooth closed subgroup. The kernel node records AV p.43's missing ground-field abelian-part assertion honestly as statement-only. For the annihilator I read iAG Proposition 11.32 (p.221), whose assertion is on every algebra's points, not just geometric points. For finite products I read Stacks varieties.tex Tag 0B2M (lemma-dimension-product-locally-algebraic), and the abelian-variety/connected-group background in Tags 03RO, 0B7Q and 0BFC. I corrected the exact 0B7Q label after checking tags/tags.

For step 1 I opened the retraction and image statements and checked ri=[n] is precisely what is needed for qi=0 and rq=0; commutativity comes from lem-sc-av-commutative and the operation identities from the two definitions cited. The image statement actually supplies an abelian variety; it is not merely an image subgroup. Factorization through ker r is checked on the defining ideal, rather than inferred only from set-theoretic image containment.

For steps 2–3 the product statement supplies the abelian source and dimension additivity; lem-sc-mult-n-isogeny supplies surjectivity and finiteness of the torsion subgroup over arbitrary k. The kernel of the addition map is identified explicitly with the scheme-theoretic intersection and is a closed subscheme of B[n], so nonreduced intersections are retained. The image dimension formula then gives dim C=dim A-dim B, with both induction dimensions strictly smaller.

Step 4 states the induction, its zero and simple bases, and the inductive assembly. Step 5 supplies the promised isogeny verification instead of hiding it in 'composition of isogenies': lem-sc-isogeny-degree gives finite flat maps, and lem-trf-finite-radicial-basechange explicitly states finite stability under base change and composition without requiring radicialness for that clause. Nonempty geometric finite fibres give surjectivity of the product, and the kernel is a finite base change. Both cited statements were read; the latter is a general geometric Mathlib leaf, not an application of the trace formula.

For steps 6–7 the image node gives an abelian subvariety of Y, the product/zero-object node rules out dimension zero for a nonzero map, and lem-sc-abelian-variety-characterization gives integrality for the short full-dimensional closed-subvariety argument written in the step. The kernel lemma supplies an actual abelian subvariety over k of the correct dimension. Source simplicity therefore applies; it does not apply directly to a nonreduced kernel. The finite conclusion comes from that lemma, with no perfectness restriction.

For step 8 I checked that lem-sc-isogeny-degree gives finite and flat, the isogeny definition supplies surjectivity, and the fpqc definition is satisfied by the one affine preimage. The annihilator acts on the full finite kernel; rank n is positive because a group scheme has an identity. For step 9 I read the statement of fpqc representable descent, then read Stacks Tag 023Q, lemma-fpqc-universal-effective-epimorphisms, and verified that the two pullbacks agree as morphisms by the displayed kernel-pair isomorphism. Descent is applied only to a singleton finite flat surjection, with scheme target X. Its uniqueness also proves the descended map is over k.

In step 10 the base-change covering node states exactly stability of fpqc coverings under base change, so it supplies the two covers f×1 and 1×f. I checked addition, identity and inverse individually; the equalities cancel covers via the uniqueness clause of representable descent. Step 11 obtains fg=[n] by cancelling f, and proves g is an isogeny using surjectivity of [n] and a closed inclusion ker g into Y[n], not by a pointwise or characteristic-prime-to-n argument.

I checked B=0 and B=A in the retraction prerequisite, A=0 and the empty product, dimension-one simple varieties, the zero map (explicitly excluded), identity isogenies and the zero abelian variety isogeny, characteristic-p multiplication and Frobenius-type infinitesimal kernels, and an imperfect base field. In particular G=mu_p and alpha_p are consistent with rank annihilation although geometric points alone would give no proof. The zero-dimensional abelian-variety conclusion uses smoothness and geometric integrality, so finite nonreduced groups do not form counterexamples. No step exceeds 2000 characters (the longest is below 800). None of the five new statements is a decomposition clause, a nonzero-simple-map clause, or the quasi-inverse clause relabelled.

## Unfinished work

This is a one-level stage-1 split: the five new nodes intentionally have no proofs and remain unsplit for later workers. No Lean was written and no compiler, Lake or build tool was run. The item itself has a complete assembly argument relative to its cited statement-only prerequisites. Server checks and delivery results are recorded below as they complete.

## Server validation

The server review_split check passed. The required deliver.py --no-push completed with exit 0 and printed OK (not pushed), commit 56bef9f2e23; all preflight checks passed. Five new nodes, zero Mathlib leaves.
