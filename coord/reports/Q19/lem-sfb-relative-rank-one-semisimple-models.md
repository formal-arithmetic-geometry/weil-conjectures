# Worker report: Q19

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-rank-one-semisimple-models.json`: item, statement unchanged, ten-step split; Mathlib searches give no match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-adjoint-rank-one-flag-curve.json`: new statement-only lemma, unsplit; no Mathlib match. Constructs the relative quotient and action used before trivializing the curve.
- `dag/nodes/sec-six-functors-basics/lem-sfb-pointed-projective-line-family.json`: new statement-only lemma, unsplit; no Mathlib match. A theorem about arbitrary smooth proper pointed families, without any group hypothesis.
- `dag/nodes/sec-six-functors-basics/lem-sfb-triangular-maximal-torus-conjugacy.json`: new statement-only lemma, unsplit; no Mathlib match. Gives the relative transporter torsor in the upper triangular subgroup.
- `citations.json`: one verbatim statement quotation for each node used in each proof step.
- `searches.jsonl`: actual Mathlib-search command log; auxiliary search and drafting files remain in this sandbox.

There are three new nodes and zero Mathlib leaves. No Lean file, repository file, or launcher script was written, and no compiler was run.

## Attachments

None. Searches of the live `lean/WeilConjectures/` for the blueprint tag, item id and relative rank-one, reductive, semisimple, PGL and torus terminology did not find a sorry-free declaration proving every clause. Abstract matrix-group declarations in Mathlib do not attach this relative scheme theorem.

## Literature wanted

WANTED: `literature/conrad-reductive-group-schemes.pdf`, Brian Conrad, *Reductive Group Schemes*, Proposition 4.2.7 and proof (printed pp.123--124), for `lem-sfb-relative-rank-one-semisimple-models`, `lem-sfb-relative-adjoint-rank-one-flag-curve`, `lem-sfb-pointed-projective-line-family`, and `lem-sfb-triangular-maximal-torus-conjugacy`.

WANTED: the same document, Proposition 4.3.4 and proof (printed pp.131--132), Proposition 4.3.1 and proof (pp.126--131), Theorem 3.3.4 and Corollaries 3.3.5--3.3.6 (pp.98--101), for the item's order-two argument and the existing relative centre, quotient and extension nodes it uses.

The author-hosted PDF `https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf` was read online at these places, including the preceding relative parabolic/quotient construction (Theorem 2.3.6, pp.72--75). It was not downloaded. This relative structural result has no single Stacks tag. I cite Conrad, not the SGA references appearing in that book. The proof is explicitly agent-origin because the document is absent locally and I supply an alternative assembly in the order-two case. For the existing geometric-fibre criterion I also read Stacks Tag 039E, label `more-morphisms/lemma-morphism-between-flat`; its statement has the flatness and local-presentation hypotheses needed here.

## Changes and problems found

The live item had no completed proof. Its statement agrees with the relative rank-one propositions, including characteristic two and nonreduced bases; I found no statement dispute and preserved its text and statement dependencies. I preserved the blueprint provenance chain, filled the proof-related fields and searched for same statements throughout the DAG and blueprint. The inherited nearest blueprint ancestor is null (confirmed by `blueprint_refs.py ancestor`), so the inherited exact `from.place` and `via` chain are retained rather than inventing an ancestor. I read the latest six-functors section, the constructible-stability unit and its direct-images proof. This lemma supplies the relative rank-one model used on that route; neither the chapter nor unit route changes.

The proof now separates a relative flag curve, its pointed trivialization, and adjustment of the torus. I reused the newly landed relative centre and central multiplicative quotient nodes rather than creating their proposed duplicates. I also reused projective frames, diagonalizable character duality, the field classification only on geometric fibres, and Gabber's central-extension splitting. The familiar sequence SL2 to PGL2 and the final kernel/surjectivity assembly are explicit elementary calculations, not new nodes. In particular no new node states either local matrix-model conclusion of this item.

The order-two argument is an agent simplification of Conrad's pushout argument: split the pullback extension over SL2, examine its restriction to mu2 by character duality, rule out the trivial restriction on geometric fibres, then write the inverse sheaf map by exactness. This avoids assuming that order-two group schemes are etale, or that geometric points determine maps between arbitrary nonreduced schemes. It does not use the root-subgroup construction that the item is intended to support.

`lem-sfb-relative-root-product-open-cell` is not used: it takes relative root subgroups as input, whereas the current item supplies a prerequisite for their construction. `sbc-lem-smooth-geometrically-reduced` is the only off-unit theorem used as a generic tool: in step 8 smoothness rules out the nonreduced geometric product with mu2 in characteristic two. Its use is declared in `split_report.tool_uses`; there is no replacement for that general smoothness property in this unit.

While checking definition citations, I corrected the new triangular lemma's group-diagram reference to `def-sc-group-scheme`; `def-pc-scheme` alone would not define those diagrams. I added explicit properness, geometric-point and fibre-product references in the new flag statement. Every new node remains statement-only, with empty proof and proof dependencies.

## Not duplicates

lem-sfb-relative-adjoint-rank-one-flag-curve vs lem-sfb-rank-one-flag-curve: the existing result is over an algebraically closed field and gives dimension one for an already represented Borel quotient; the new result constructs a relative smooth proper quotient, section and action over a Noetherian base.

lem-sfb-relative-adjoint-rank-one-flag-curve vs lem-sfb-rank-one-adjoint-projective-linear: the existing adjoint quotient result is over an algebraically closed field; the new statement is relative and supplies a curve with section and its fibrewise action, not a relative isomorphism with PGL2.

lem-sfb-relative-adjoint-rank-one-flag-curve vs lem-sfb-borel-quotient-proper-geometry: the existing result assumes a quotient over an algebraically closed field; it does not construct this family or its action over a ring.

lem-sfb-relative-adjoint-rank-one-flag-curve vs lem-sfb-reductive-cocharacter-parabolic-geometry: the existing result constructs a cocharacter quotient over a field, not over an arbitrary Noetherian base.

lem-sfb-relative-adjoint-rank-one-flag-curve vs lem-sfb-borel-scheme-normalizer: the existing result identifies a normalizer over an algebraically closed field, not the relative flag family.

lem-sfb-relative-adjoint-rank-one-flag-curve vs lem-sfb-relative-root-product-open-cell: the existing result assumes relative root subgroup data and provides an open cell; the new statement supplies a relative flag quotient without that input.

lem-sfb-relative-adjoint-rank-one-flag-curve vs lem-sfb-relative-rank-one-semisimple-models: the new flag lemma, extracted from the beginning of Conrad's Proposition 4.2.7 proof, gives a relative curve and a fibrewise action, not a Zariski local group or pair isomorphism. Pointed-family trivialization, the relative automorphism theorem, the geometric-fibre test and triangular conjugacy are still required to prove the item's first clause.

lem-sfb-pointed-projective-line-family vs lem-trf-pointed-genus-zero-projective-line: the existing result is for an integral curve over a field with a degree-one line bundle; the new result is for smooth proper families over nonreduced Noetherian schemes, with a prescribed section and pointed local trivializations.

lem-sfb-pointed-projective-line-family vs lem-trf-genus-zero-smooth-proper-line: the existing result is a curve over an algebraically closed field; it gives no trivialization of a family over its base.

lem-sfb-pointed-projective-line-family vs lem-sfb-fibrewise-very-ample-evaluation: the existing evaluation theorem starts with a specified line bundle satisfying fibrewise very-ampleness and cohomological assumptions. It does not construct that bundle from a section or provide the pointed trivialization asserted here. This is a genuine standard relative curve lemma, whose future split can use that evaluation node.

lem-sfb-pointed-projective-line-family vs lem-sfb-relative-rank-one-semisimple-models: despite the shared source proof, the new statement has no group hypothesis or group-model conclusion; it trivializes arbitrary pointed smooth proper P1 families.

lem-sfb-triangular-maximal-torus-conjugacy vs lem-sfb-borel-maximal-torus-conjugacy: the existing conjugacy result is over an algebraically closed field; the new result represents a relative transporter and asserts its Zariski local sections over Noetherian rings.

lem-sfb-triangular-maximal-torus-conjugacy vs lem-sfb-torus-normalizer-borel-transitivity: the existing result conjugates Borel subgroups containing a fixed torus over an algebraically closed field; the new result conjugates a varying relative torus inside a specified triangular subgroup and describes its transporter torsor.

lem-sfb-triangular-maximal-torus-conjugacy vs lem-sfb-relative-rank-one-semisimple-models: the new statement already assumes the ambient group is PGL2 and the torus is triangular. It proves the final transporter assertion, not the existence of the item's matrix-model isomorphism.

lem-sfb-relative-adjoint-rank-one-flag-curve vs lem-sfb-pointed-projective-line-family: the first constructs a homogeneous curve and action from a group; the second trivializes arbitrary pointed curve families and contains no group action.

lem-sfb-relative-adjoint-rank-one-flag-curve vs lem-sfb-triangular-maximal-torus-conjugacy: the first constructs a flag curve; the second starts inside explicit PGL2 and constructs a conjugating transporter.

lem-sfb-pointed-projective-line-family vs lem-sfb-triangular-maximal-torus-conjugacy: the first concerns smooth proper curves with sections; the second concerns subgroup schemes and transporter torsors. Neither conclusion implies the other's directly.

## Mathlib searches

For each of the three new nodes I ran LeanFinder, Loogle, Mathlib grep through `msearch.py`, LeanSearch, and a second natural-language LeanFinder phrasing. The exact queries, returned log records and verdicts are in the nodes and `searches.jsonl`. I read the hits rather than inferring absence from names alone. Flag-curve searches found general affine-space and ideal-quotient lemmas and abstract group material, not relative Borel quotients. Pointed-family searches found topological bundle trivializations and projective Weierstrass/elliptic geometry, not the required smooth proper curve-family theorem. Triangular-transporter searches found abstract matrix or arithmetic subgroup material, not scheme-theoretic tori or transporter representability.

For the item I retained the inherited actual search records, read their hits, and ran additional Q19 searches with both matrix-model and semisimple-group phrasing. `Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'` and its companions describe an abstract matrix-group centre; `GeneralLinearGroup.toPGL_ker` describes an abstract quotient kernel. Neither classifies relative reductive group schemes, and neither is a one-line specialization for these objects. A candidate local isomorphism criterion for flat monomorphisms requires different assumptions and cannot replace the existing geometric-fibre lemma in one line. All actual services returned results in the recorded searches; no failed service is represented as a no-match. Proposed centre, quotient, fibrewise criterion and central-cover nodes were discarded once existing statements or elementary calculations sufficed; their searches remain logged, without creating nodes.

## Review by Q19

I checked delivery-errors B--E against the node statements and the sources, not just the graph. For each new statement I checked that it introduces its base, all schemes and subgroups, the relevant quotient or transporter functor, and the exact topology. No new statement contains its proof sketch. None is a clause merely renaming the item. DAG, source-place, and whole-blueprint searches were made before retaining these three nodes, and project Lean-source searches found no completed exact declaration for them.

For the new flag-curve lemma I read the construction in Conrad Proposition 4.2.7 through the section and the action on geometric fibres, together with Theorem 2.3.6 for the relative quotient. The hypotheses are a split maximal torus, rank one, and trivial scheme-theoretic centre, over a Noetherian ring. The new node does not assume the relative PGL2 conclusion it will help prove. For the pointed-family lemma I read the next paragraph on the line bundle of the section, the rank-two direct image and evaluation: the smooth section provides the degree-one divisor, so the source really treats a family rather than just geometric fibres. For the triangular lemma I read the final paragraph on the torus transporter and its Gm-torsor; the conclusion is Zariski local, not a globally chosen conjugating matrix. Its left D action is consistent with the equation bTb^{-1}=D.

Step 1 uses the projective-frame statement's actual local matrix lifts. The quadratic extension is free on 1,t and t is a unit because its square is a unit; determinant normalization needs no etaleness or division by two. The kernel and inverse-image diagonal assertions are matrix equations with faithfully flat descent of their entries. They therefore need no new central-cover lemma.

Step 2 uses exactly the flag lemma's relative quotient, identity section, B-fixity and fibre action. Its trivial-centre hypothesis follows from the explicitly split augmentation of the rank-one centre algebra, not from a statement only about geometric points. Restricting to opens preserves the hypotheses.

Step 3 uses the pointed-family node for a section-preserving isomorphism, projective frames for Aut(P1)=PGL2, and the flag node for the action on every geometric fibre. I opened the geometric-fibre criterion: its isomorphism clause, not just an open-immersion conclusion, applies to a locally finitely presented morphism between smooth S-schemes. The base remains Noetherian; I included the finite-generator/kernel argument establishing local finite presentation, with the actual Noetherian-ring definition cited. Smoothness of PGL2 is in the frames statement. The containment in B-infinity is the lower-left matrix equation, not a set-theoretic containment unsupported on nilpotents.

Step 4 uses exactly the triangular lemma's local sections and conjugacy equation. Its torus hypothesis holds because the action map has already been proved an isomorphism in step 3. This completes the trivial-centre assertion for later use on Q, rather than assuming the original item recursively.

Step 5 uses the centre node's explicit multiplicative-type representation and base-change clause. Rank two forces its diagonalizable character group to have two elements. The duality node controls all homomorphisms over arbitrary rings, including nonreduced ones, and hence makes Aut(mu2) trivial on all overlaps. Uniqueness glues the fppf identifications; this is not an illicit passage from geometric points to maps of arbitrary schemes.

Step 6 uses the central multiplicative quotient node for reductivity, its exact kernel, centre formula, torus correspondence and base change. Its hypotheses hold for Z by step 5, with no smoothness of Z required. The duality node gives the torus quotient as D(ker u); the displayed basis proves splitness, so there is no hidden assertion that every torus quotient is split. The rank-one classification node is explicitly over algebraically closed fields and is used only there, after taking geometric fibres. Finite centre of rank two excludes its positive-dimensional central-torus and GL2 cases and the trivial-centre PGL2 case. Thus Q has rank one, and steps 2--4 apply to Q on affine refinements.

Step 7 uses the existing extension-splitting node, whose statement really permits separated commutative Z and fppf group sheaves without a smoothness or invertibility-of-two assumption. The pullback extension has exactly these hypotheses. Its splitting produces f with p'f=q0. I do not take a construction merely mentioned in the proof of that node.

Step 8 again uses character duality's locally constant lattice maps, not a classification of points of mu2. Those maps have only the zero and identity possibilities for Z/2. The explicit inverse proves the product identification if the restriction is zero. In odd characteristic this violates connectedness; in characteristic two the tensor product has a genuine nonzero square-zero element. The cited smooth-geometric-reducedness statement supplies precisely the contradiction to smoothness. Local constancy plus these tests eliminates the zero possibility even on nonreduced and disconnected bases.

Step 9 uses the quotient node's exact torus inverse-image correspondence, and the two exact sequences already proved. I wrote out injectivity, local surjectivity and gluing of preimages, rather than just saying that a diagram transports the conclusion. This is elementary sheaf algebra; the torus identification follows by taking inverse images of the same D. Step 10 writes restriction to affine refinements and pullback of inverse maps explicitly, so arbitrary base change requires no reducedness or Noetherianness of the new base.

Small-case checks: over a field the flag lemma specializes to the familiar PGL2/B=P1 action with the identity coset fixed by B; a torus of rank zero cannot meet its semisimple-rank-one hypothesis. Over a nonreduced ring the new flag statement only asserts the action is an isomorphism on geometric fibres, leaving the legitimate relative isomorphism test to step 3. For the pointed-family lemma the trivial P1 family with an arbitrary section is locally pointed-trivial by choosing a basis of its quotient line, and a projective bundle from a nontrivial rank-two vector bundle needs only a local, not global, trivialization. A nonsplit conic over a field has no rational section, so is not a counterexample. Empty base for that general lemma is vacuous. For the triangular lemma, T=D gives Y=D (the triangular normalizer has no Weyl involution); conjugating D by a unipotent triangular matrix produces the expected coset transporter, with D acting freely on the left. The statement never claims that a Gm torsor has a global section. These checks also work in characteristic two. For the item's order-two case mu2 is kept as a group scheme in characteristic two; replacing it by its single geometric point would be wrong. Disconnected and nilpotent base changes are allowed throughout by the duality and quotient statements.

All proof steps are shorter than 2000 characters. I checked the shorter steps as well for concealed independent lemmas: the standard relative curve and transporter facts are the new nodes, and the remaining non-elementary inputs are existing cited nodes. The matrix normalization, rank-one augmentation, lattice basis, kernel dichotomy calculation and sheaf exactness are written out in the item. `citations.json` covers every uses entry with a verbatim part of the cited node's statement. The final server dry run remains the required graph and delivery validation before push.

## Unfinished work

No part of this one-level split remains unprovided. The three supporting lemmas deliberately remain unsplit, as stage 1 requires; they are future work items, not claimed as proved Lean declarations. The local source PDF is wanted as recorded above. Delivery validation and push are performed after this report is written.
