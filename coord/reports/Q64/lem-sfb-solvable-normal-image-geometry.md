# Stage-1 delivery: lem-sfb-solvable-normal-image-geometry

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-solvable-normal-image-geometry.json`: existing statement, now split into seven proof steps; no Mathlib match for the item.
- `citations.json`: verbatim statements for each node cited by each step.

New nodes: 0. New Mathlib leaves: 0. Supporting lemmas already exist in the live DAG, so none were duplicated.

## Attachments

None. Searched the whole `lean/WeilConjectures/` for the item tag and solvability, and the group-scheme sources for normal images. There is no project declaration stating all clauses. The existing `GroupScheme/Image.lean` results concern proper source group schemes and image group structures, not this assertion for arbitrary affine finite-type groups. Abstract-group results from Mathlib are not attachments or matches for group schemes.

## WANTED

None. All mathematical source material used is present.

## What required repair

The node had a statement but no proof. Its statement is retained verbatim. In particular neither kernel is assumed finite or smooth. The map j is only explicitly called a closed immersion in the statement: step 1 proves it is a homomorphism, using the quotient map, rather than adding that hypothesis.

The inherited `blueprint.from.node` is null; `tools/blueprint_refs.py ancestor` reports that fact. The whole inherited via chain and place are retained. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and the current `sk-thm-sf-ctf-stability-direct-images.proof.md`. The current proof's paragraph (3) is the proper/open compactification assembly; the item's inherited detailed ancestry records the intermediate alteration and Milne inputs of its existing branch. This split supplies the image input within that branch, without changing a chapter or unit route. Whole-blueprint searches for solvability and normal images found no blueprint node stating this item. Existing DAG nodes for derived groups, geometrically reduced group smoothness, and affine image factorization supply the supporting facts.

Mathlib searches are in `searches.jsonl`; all five completed successfully. The semantic hits include `solvable_of_surjective`, `solvable_quotient_of_solvable`, `Subgroup.Normal.map`, Lie-algebra solvability, and general flat/smooth morphisms. These do not give a scheme-theoretic image theorem. The grep also finds `smooth_of_grpObj`; its exact geometric-reducedness input is already the existing leaf `lem-sfb-geometrically-reduced-group-smooth`, which the proof cites. The two different LeanFinder phrasings were both read. The item's pre-existing search history is retained, and the searches made for this delivery are appended with their actual log records.

## Unfinished work

None in this one-level split. Existing unsplit dependency nodes remain their own items. No Lean was written or compiled and the read clone was not modified.

## Not duplicates

No new nodes, hence no new/existing pairs to distinguish. In particular I reused `lem-sfb-smooth-connected-derived-subgroup`, `lem-sfb-affine-homomorphism-flat-image`, `lem-sfb-geometrically-reduced-group-smooth`, and the two faithful-flatness nodes instead of creating quotient-smoothness, quotient-connectedness, quotient-solvability, or normal-image clause nodes.

## Review by Q64

I read Milne, Algebraic Groups (2017), Proposition 1.62(b) and its following nonsmooth-kernel example (printed p.24); the Homomorphism Theorem 5.39, uniqueness Remark 5.40 and image Remark 5.42 (p.108); Proposition 5.59(b) (p.114); the commutator description in Proposition 6.18 and Corollary 6.19 (p.129), Proposition 6.27 and its image-series proof (p.131), Proposition 6.30 and its derived-series proof (p.132); and the proof of Lemma 19.14 (p.400). The text says normality follows from surjectivity; I supplied the affine ideal argument so the proof does not mistakenly assume pointwise surjectivity over every test algebra. There are no new nodes needing another source review.

For step 1 I opened the statement of `lem-weil-pbc-faithfully-flat-universally-injective`: with its arbitrary module specialized to the source ring it gives exactly the coordinate injection. I also read Stacks Tag 05CK, `algebra.tex`, lemma-faithfully-flat-universally-injective. `def-weil-affine-spectrum` gives the affine algebra/morphism correspondence, the tensor-pushout node gives the tensor algebra multiplication and universal property, and `def-weil-closed-immersion` gives the quotient-ring description of affine closed immersions. The splitting of an injection as a vector-space map, tensoring its left inverse, and killing an ideal are written explicitly. These are elementary coordinate arguments, not a new descent theorem. The left inverse is only linear, which suffices for injectivity; no algebra retraction is claimed. The same argument proves multiplication compatibility for j.

For step 2, `sbc-lem-smooth-geometrically-reduced` states geometric reducedness of smooth fibres; over Spec F there is exactly the fibre N itself. I read Stacks Tag 056T, varieties.tex, lemma-smooth-geometrically-normal, which explicitly states geometric reducedness for smooth schemes over a field. The reduced-scheme definition identifies affine reducedness with absence of nilpotents in its global ring. Tensoring the linear left inverse works for every extension field L, so the coordinate injection proves geometric reducedness of I, not just reducedness over F. The exact statement of `lem-sfb-geometrically-reduced-group-smooth` requires a locally finite-type group scheme and geometrically reducedness: both are now available. Its Stacks source Tags 047N/047P concerns group smoothness; I read the latter perfect-field statement as well. This is precisely Milne's argument and does not assume q is smooth.

For step 3, I opened `lem-weil-pbc-faithfully-flat-surjective-spectrum` and Stacks Tag 00HQ, algebra.tex, lemma-ff-rings. It really gives surjectivity on prime spectra from faithful flatness. Combined with the connected-space definition, inverse images of a hypothetical clopen partition give the displayed contradiction. Surjectivity of q on arbitrary R-points is neither stated nor used. Nonemptiness is guaranteed by the identity section.

For step 4, the statement of `lem-sfb-smooth-connected-derived-subgroup` gives smoothness, connectedness, affineness, finite type and the smallest-closed-subgroup property needed at each iteration. It applies to N and each subsequent derived term, with the same algebraically closed F. The statement of `lem-sfb-affine-homomorphism-flat-image` applies to every restricted map N_r -> I and gives both the closed image and a coordinate faithfully flat map. This is stronger than just existence of an image subscheme and is exactly what step 5 uses. The source-derived series terminates by the item's stated definition of solvability. The terminal trivial subgroup is closed because its counit is a surjective algebra map.

For step 5, I checked that the derived-subgroup node asserts factorization of the commutator morphism, not merely a statement about rational points. The universal-injection node gives injectivity of each u_r pullback, and the explicit tensor argument gives injectivity for u_r times u_r. Consequently the ideal test descends the displayed commutator factorization. This is elementary from the already cited statements and step 1; it does not import a solvable-quotient theorem. There is no use of the proof of a cited node.

For step 6, the induction is on the assertion D^r(I) lies in J_r, with base, induction step and terminal case written separately. The cited derived-subgroup statement gives its minimality among all closed subgroups containing the commutator. The intersection with J_{r+1} is such a closed subgroup of D^r(I); its coordinate ideal is explicitly the sum of the ambient ideals. All successive D^r(I) remain smooth connected by the same cited statement. No equality of image and target derived subgroups, and no unjustified interchange of a quotient and derived series, is assumed. The chosen finite series J_r therefore proves termination of the actual derived series of I.

For step 7, I reread `def-sc-group-scheme-subgroup`: normality is required on every F-algebra, and this is exactly the conclusion. It also supplies source normality on the universal pair over F[G] tensor F[N], which proves factorization of source conjugation as a scheme morphism. The identity c(f(g),q(n))=f(gng^{-1}) is a homomorphism identity. Coordinate injectivity of f and q, and tensoring their linear left inverses, descend the vanishing of the defining ideal without requiring H or G reduced or smooth. Using h^{-1} upgrades conjugation containment to equality. This checks scheme normality even for nonreduced test rings.

I checked B--E of delivery-errors.md against the written split. There are no new statement-only nodes, no restated clauses masquerading as lemmas, no new-source citation without a node, and no per-degree or coefficient-category issue. Every cited node's statement is copied verbatim into citations.json. The generic off-unit tools are declared in split_report.tool_uses. Every proof step is shorter than 2000 characters. The item is unchanged, so there is no statement dispute.

Small cases: N=e (t=0), q an isomorphism, f an isomorphism, and q with trivial image all satisfy the argument. In characteristic p, Frobenius on G_a has nonsmooth kernel alpha_p, yet its image is smooth and connected; the proof uses coordinate injection, not a smooth quotient-map assertion. Frobenius on G_m similarly allows kernel mu_p. A nonreduced ambient factor, for example G=N times alpha_p with projection onto N, does not break the tensor/ideal normality proof. The proof never replaces scheme normality by normality of F-points.
