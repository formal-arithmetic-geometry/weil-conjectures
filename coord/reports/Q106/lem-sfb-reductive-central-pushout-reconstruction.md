# Q106 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-reductive-central-pushout-reconstruction.json: item split in six steps; statement retained, no new hypotheses.
- dag/nodes/sec-six-functors-basics/lem-sfb-central-diagonalizable-derived-intersection-finite.json: new statement-only lemma, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-diagonalizable-quotient-character-kernel.json: new statement-only lemma, unsplit; no Mathlib match.
- report.md and citations.json: substantive self-review and verbatim statement quotations for every proof citation.
- searches.jsonl, search-results.json and diagonalizable-search-results.json: required command log and full search answers actually read; write_split.py is a sandbox-only JSON preparation helper.

## Attachments

None. I searched the live lean/WeilConjectures source for the blueprint tag, central pushouts, reductive groups, central isogenies, and derived subgroup terminology. The hits concerning semisimple representations, Lie algebras, and GeneralLinear derived Hopf ideals do not state this item or either new statement. No compilation was attempted.

## WANTED

None: the source used is literature/milne-algebraic-groups_iAG2017.pdf already in the repository. No SGA source is used.

## What was wrong or required care

The item was statement-only. Its statement is correct, including noninjective centre maps and nonreduced kernels. The easy-looking citations to the existing reductive-centre, root-centre, central-torus product, and simply connected cover nodes would introduce a cycle: their existing dependency closures lead through reductive-borel-pair-structure, reductive-rank-one-reflections and split-rank-one-classification back to this item. I did not edit those existing nodes. Instead I derived centre containment from the independently available maximal-torus self-centralizer, and used the item's explicit perfectness hypothesis on S to prove G=Z(G)G^der. No appeal to semisimple groups being perfect is needed. The explicit universal property in the item requires only a smooth connected source, not semisimplicity of that source, so it applies directly to G^der once the kernel is shown finite and diagonalizable.

Milne Example 19.25 calls Z(G) to G/G^der an isogeny even though its source need not be smooth or connected; the delivery uses only its fppf quotient and kernel assertions. Milne Proposition 19.27 says both arrows into G(phi) are injective; for the arrow from H this must mean H/ker(phi), as the displayed source in the diagram indicates. The current item already has this correct quotient. Neither remark requires a change to its statement.

The existing blueprint ancestry has from.node=null: tools/blueprint_refs.py ancestor returns None, and I preserved that ancestry. I read the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof, and the chapter/unit records. The inherited supporting-input route is recorded in from.place and split_report.blueprint; the latest direct-image proof is not itself a source for the algebraic group argument. No chapter or unit file is changed.

## Not duplicates

lem-sfb-central-diagonalizable-derived-intersection-finite vs lem-sfb-central-torus-semisimple-derived-product: the old node assumes a central torus with semisimple quotient and concludes a product decomposition and semisimplicity. The new lemma concerns every central diagonalizable subgroup of every smooth connected affine group, including a nonreduced or disconnected subgroup, and asserts only finiteness of its intersection with the derived group. The old node is not applicable before establishing semisimplicity and leads back to the item through its perfectness dependency.

lem-sfb-central-diagonalizable-derived-intersection-finite vs lem-sfb-central-torus-faithful-weight-blocks: the old statement constructs a representation and torus weight blocks; it does not assert the finite intersection, and assumes a torus rather than an arbitrary diagonalizable central subgroup.

lem-sfb-diagonalizable-quotient-character-kernel vs lem-sfb-multiplicative-character-antiduality: the old statement gives character antiequivalence, closed-immersion detection and scalar extension; it does not state exactness or describe the represented fppf cokernel. The new statement isolates Theorem 12.9(b),(c), not the already recorded equivalence of (a).

lem-sfb-diagonalizable-quotient-character-kernel vs lem-sfb-split-torus-subgroups-diagonalizable: the old statement concerns closed subgroups of split tori; a quotient of a possibly nonreduced diagonalizable group is not that assertion.

lem-sfb-diagonalizable-quotient-character-kernel vs lem-sfb-torus-homomorphism-image: the old statement assumes its source is a smooth connected torus and concludes its image is a torus. The new statement permits arbitrary finitely generated character groups and computes the character group of the fppf cokernel.

I searched the entire DAG for the source numbers, diagonalizable quotients, central intersections with derived groups, and the proposed ids. I also ran blueprint_refs searches for reductive centre, multiplicative covering, central torus, diagonalizable, commutator, derived subgroup, central diagonalizable, 12.46 and diagonalizable quotient. No imported blueprint node supplies either new statement. The only derived-subgroup blueprint hit is sk-i-restriction about monodromy and abstract groups. The broad derived/multiplicative searches also contain unrelated derived-category and multiplicative-group notation hits, not another copy of these statements.

## Review by Q106

I read Milne printed pp.402--405 (Proposition 19.21, Lemma 19.23, Examples 19.24--19.25, Definition 19.26, Proposition 19.27, Proposition 19.29 and Remark 19.30). I checked the lifting argument against the actual definition of universal covering in the item rather than assuming it applies to G, whose central kernel would usually have positive dimension. I also read pp.245--246, the proof of Proposition 12.46(a), and pp.232--236, Theorems 12.8--12.9, Theorem 12.12 and Remark 12.13 and Definition 12.14. The first new lemma is the generalization of that determinant argument to central diagonalizable groups: arbitrary diagonalizable groups still have character weight decompositions, the central action preserves each block, each determinant kills the derived group, and a central element in it satisfies chi_i^dim(V_i)=1 for every weight. Faithfulness of the weights embeds this intersection in the finite product of the corresponding roots-of-unity schemes. This is a general lemma, not a clause of the reconstruction theorem, and its proof is not inserted into its statement. The second new lemma is precisely the exactness/quotient assertion in 12.9(b),(c); its direction is checked with alpha:M to N inducing D(N) to D(M), so its cokernel has character group ker(alpha).

For step 1 I opened each of the five cited nodes. Centre-base-change represents the all-algebra centre as a closed normal commutative subgroup; Borel-conjugation-cover explicitly states existence of Borels; Borel-maximal-torus-conjugacy states that a Borel contains a torus maximal in G; self-centralizer explicitly asserts equality of functors even on nonreduced algebras; split-torus-subgroups gives the actual group-algebra presentation. G is smooth connected reductive over the algebraically closed F throughout. The centre inclusion is checked at the universal point, so it is a scheme-theoretic closed inclusion, not a conclusion from geometric points.

For step 2 I opened smooth-connected-derived-subgroup, affine-homomorphism-flat-image and affine-normal-quotient-geometry. They provide respectively smooth connected normal H, the closed faithfully flat image I, and the represented fppf quotients and their universal properties. Normality is checked by conjugating local products dh. The common quotient is commutative because it kills H; its composite with the given perfect S is trivial since the kernel contains commutators, and faithful-flat local surjectivity of q forces it to be trivial. This proves the product equality instead of quoting the proposition whose proof depends on the item.

For step 3 the new finite-intersection node applies with C=D and the same G, without assuming that D is smooth. The existing split-torus-subgroups statement supplies diagonalizability of K because K lies in the previously chosen T. The quotient node identifies H/K with Q after the explicit local lifting argument from G=DH; hence its p is faithfully flat. H is smooth connected by step 2, K is finite by the new node, central by inclusion in Z(G), and diagonalizable by the torus inclusion. These are exactly the hypotheses of the universal property supplied in the item's statement. This gives a genuine lift through H, not a supposed lift through the positive-dimensional central extension G to Q.

For step 4 the sole citation is the fppf quotient node. The substantive work is the written kernel calculation: q(s)=1 if and only if s lies in Z(S), and then d=phi(s)^(-1). Local lifts through q give local surjectivity of m, so its quotient is G. This is marked elementary relative to that quotient theorem because it is the explicit two-equation computation and does not invoke any additional algebraic-group structure theorem.

For step 5 I reopened the flat-image and quotient statements: flat image supplies the closed subgroup J and local lifts of its points; the quotient theorem identifies a faithfully flat homomorphism with its kernel quotient. Locally expressing any pair as v(s_i)d_i shows their commutator equals v([s_1,s_2]), since D is central. Closed membership descends on the fppf site, so H's minimality forces J=H. The kernel of v is contained in ker(q)=Z(S), so it is exactly ker(phi). Thus the image and quotient assertions are established without assuming perfectness of H or importing a second theorem on images of derived subgroups.

For step 6 I opened the quotient node's smoothness/connectedness clauses and the largest-subtorus node's explicit assertion that a smooth connected multiplicative-type group is a torus. Local lifting through u identifies im(phi) with K, including infinitesimal points, and D/K with G/H. The new quotient-character lemma applies to the diagonalizable D and its closed subgroup K; it asserts exactly that this quotient is diagonalizable, which is absent from the existing antiduality node's statement. G/H is smooth connected because G is, not because D is. These checks discharge the torus hypothesis without mistakenly assuming that an arbitrary connected diagonalizable scheme is smooth.

I tested the statements and construction on G=1, a split torus (S=H=1), GL_n with S=SL_n and phi:mu_n to G_m, the adjoint PGL_n case (D=1 and phi trivial), and SL_n (phi the identity on mu_n). In characteristic p dividing n, mu_n is nonreduced, but the finite-intersection statement, kernel graph, and quotient computations are still schematic and valid. The first new lemma also allows central mu_p and disconnected finite diagonalizable C; it does not generalize to arbitrary central unipotent subgroups, which would be false for the Heisenberg group. The diagonalizable quotient lemma was checked for alpha=0, identity, multiplication by p in characteristic p, and the map Z to Z/nZ (mu_n inclusion into G_m, cokernel character lattice nZ). All directions agree.

The Mathlib answers were read from the required msearch commands and saved in the sandbox; both phrasings of each semantic search were tried. Abstract group finiteness requires extra hypotheses such as a finite commutator set, and characteristic-zero Lie results say nothing about the centre scheme. The HopfAlgebra quotient hits were checked in Mathlib/RingTheory/HopfAlgebra/Quotient.lean lines 94--119: they construct a quotient coordinate algebra by a Hopf ideal, not a group quotient or a character exactness statement. These are not one-line specializations of either new lemma. No failed service is reported as a successful empty search.

I checked delivery-errors B--E against all three files: self-contained objects and inline meanings, sourced statement-only new nodes, no elementary or clause-copy node, actual searches, no definition used as a theorem, citations restricted to their stated content, no added hypotheses, explicit fppf comparisons, correct all-algebra kernels, and no circular dependence. Every step is under 2000 characters. citations.json quotes each used statement verbatim; longer quotations are used for the general image and quotient nodes because several clauses are needed.

## Unfinished work

Neither new node is split, as required for a one-level stage-1 delivery. There is no unfinished step in the item's natural-language proof. Independent maintainer review remains responsible for mathematical acceptance.
