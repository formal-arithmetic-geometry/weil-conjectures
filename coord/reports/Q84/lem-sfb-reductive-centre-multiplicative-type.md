# Worker report: lem-sfb-reductive-centre-multiplicative-type

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-reductive-centre-multiplicative-type.json: item split; unchanged statement; three proof steps following Milne Corollary 17.62(a).
- dag/nodes/sec-six-functors-basics/lem-sfb-geometrically-maximal-torus-exists.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-reductive-torus-self-centralizer.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim statement excerpts for every citation in the item's proof.

## Attachments

None. Searched the live lean/WeilConjectures source for the blueprint tag and for reductive groups, multiplicative type, maximal tori and scheme-theoretic centres. The reductive Lie-algebra files do not state this group-scheme result. No Lean files were written and no compiler was run.

## WANTED

None. Milne, Algebraic Groups (2017), is available locally. No SGA source is used.

## Corrections and route

The statement is correct and was retained. The imported item had no proof. Its source points to Corollary 17.62(a), printed p.372; I read that proof and Proposition 17.61(a) on the same page, together with Corollary 17.83 on p.379 and Proposition 1.92 and the following paragraph on pp.33--34. The new inputs are exactly the geometric maximal-torus existence and self-centralization needed by this proof. The item carries the argument that the centre lies in that torus and hence is of multiplicative type; neither new node restates the item or its conclusion.

Read GOAL.md, SETUP.md's three levels, the chapter and unit records, and the latest blueprint's six-functor stability unit and direct-images proof (3). This is a supporting Milne lemma in the already-existing PGL/projective stable-moduli branch of the alteration route; no unit or chapter route is changed. blueprint_refs.py ancestor reports None for this seeded ancestry; the existing from.node is accordingly retained as null and the new nodes use null with the inherited via chain extended by this item. Their places explicitly name the existing direct-images ancestry and the precise Milne input. No blueprint statement update applies to this non-blueprint auxiliary lemma.

## Searches and not duplicates

Searched all dag/nodes statements and sources for maximal torus/tori, centralizers, multiplicative type, and Milne 17.61, 17.83 and 17.84. Ran blueprint_refs.py search for maximal torus, torus, reductive, centralizer and multiplicative type. The first, second, third and fifth queries find no blueprint nodes. The three centralizer matches concern characteristic-zero linear/Lie geometry, not arbitrary-characteristic reductive group schemes. The live source has no declaration stating either new lemma.

The existing lem-sfb-affine-group-centre-base-change supplies representability of the centre and is cited instead of being duplicated. The existing lem-sfb-rho-section-modules contains torus existence only for semisimple simply connected groups over an algebraically closed field; it neither supplies a torus over an arbitrary base field nor applies to the present general reductive group. The reductive-torus-simply-connected-cover node concerns a central cover, not maximal-torus existence or centralizers.

## Not duplicates

lem-sfb-geometrically-maximal-torus-exists vs lem-sfb-rho-section-modules: the new assertion is torus existence over any field for any smooth geometrically connected affine group; the existing assertion concerns a semisimple simply connected group over an algebraically closed field with additional representation-theoretic structure.

lem-sfb-reductive-torus-self-centralizer vs lem-sfb-affine-group-centre-base-change: the new assertion identifies the centralizer of a geometrically maximal torus with that torus; the existing node represents the centralizer of the whole group and proves field base change, with no torus assertion.

All Mathlib queries were run through the required msearch.py and their actual output is in the sandbox. For each node and the item I ran two distinct semantic phrasings, Loogle, source grep and LeanSearch. All services answered. Read the hits: abstract Subgroup.centralizer and centre lemmas do not yield a group-scheme centralizer identity. LieAlgebra.exists_isCartanSubalgebra_engel and LieSubalgebra.IsCartanSubalgebra.self_normalizing concern Lie algebras, not maximal algebraic tori. LieGroup hits refer to manifolds. The SpecialLinearGroup centre/roots-of-unity equivalence is specific to SL and supplies no general reductive-group result. I read these candidates in Mathlib/Algebra/Lie/CartanExists.lean at 357--377, CartanSubalgebra.lean at 48--61, GroupTheory/Subgroup/Centralizer.lean at 26--39, LinearAlgebra/SpecialLinearGroup.lean at 422--438, and Algebra/Lie/Semisimple/Defs.lean at 69--77. No leaf is claimed.

## Review by Q84

I checked B--E against the actual sources and node statements. For the item I read Milne Corollary 17.62(a), printed p.372: it chooses a maximal torus and uses Z(G) contained in C_G(T)=T. For the first new node I read Corollary 17.83, p.379, which gives a maximal geometric torus defined over the base field; it needs smooth connected affine finite-type groups, as stipulated in our node (our geometric connectedness is sufficient). For the second I read Proposition 17.61(a), p.372: its hypothesis is that the chosen torus becomes maximal over the algebraic closure, and its conclusion is the scheme-theoretic equality C_G(T)=T. The definition of C_G(T) is the all-test-algebras definition from Proposition 1.92, pp.33--34. These are non-elementary structural inputs, not elementary new nodes. Both are self-contained statement-only nodes, with empty proof/dependency lists and explicit definitions of torus, maximality and reductivity where used. Their statement dependency files were opened and actually define the named notions.

Step 1 cites lem-sfb-affine-group-centre-base-change for its explicit sentence representing Z(G) as a closed subgroup and lem-sfb-geometrically-maximal-torus-exists for its existence sentence. The former applies to any affine finite-type group; the latter applies because G has the stated smoothness and geometric connectedness. Step 2 cites the exact functor equality of lem-sfb-reductive-torus-self-centralizer. Reductivity is a hypothesis of our item and geometric maximality is supplied by step 1. The containment of functors is written out on every A and every A-algebra A', so this step never infers a subscheme inclusion merely from geometric points. The subsequent surjection k[T] to k[Z(G)] follows from factorization of the already-surjective k[G] map. Step 3 needs no further theorem: it explicitly lifts finite sums in the tensor product to preserve that surjection after base change, then applies the given definition of multiplicative type and the defining split form of T over the algebraic closure. All three steps are shorter than 2000 characters; total assembly proof is below 3000 characters. Every cited node's statement was opened and its used clause copied verbatim into citations.json, rather than extracted from its proof.

Checked small cases: G=1 allows the rank-zero torus and yields Z(G)=1; a torus G allows T=G, so the conclusion includes nonsplit tori over imperfect or finite base fields. GL_n has scalar centre contained in its diagonal maximal torus after splitting. SL_p in characteristic p has centre mu_p, which is non-smooth: the all-algebra centralizer equality and the closed-subgroup definition preserve this case, while a proof using only geometric points would lose it. The first new node also permits a unipotent H, whose maximal torus can be trivial; reductivity is therefore required only by the second node. No assumption of characteristic zero, perfectness, base-field splitting, or smoothness of the centre has slipped in. No statement dispute was found. During writing I made the closed-immersion factorization explicit instead of leaving the scheme inclusion implicit; no source statement needed correction.

## Unfinished work

No unfinished work on this one-level split. The two non-Mathlib structural inputs remain statement-only for later splitting, as required.
