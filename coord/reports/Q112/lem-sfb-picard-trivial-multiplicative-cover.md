# Stage-1 delivery: lem-sfb-picard-trivial-multiplicative-cover

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-picard-trivial-multiplicative-cover.json: item, split; statement unchanged; five proof steps.
- lem-sfb-flag-effective-picard-generators.json: statement, unsplit; no Mathlib match. Milne 18.21, effective generators on G/B.
- lem-sfb-flag-projective-linear-system.json: statement, unsplit; no Mathlib match. Projective complete linear system on G/B and the tautological linear action, Milne 18.12--18.13 and the paragraph of 18.22 beginning Let V.
- lem-sfb-projective-representation-smooth-lift.json: statement, unsplit; no Mathlib match. Lift an arbitrary projective representation through a smooth connected multiplicative cover, with the concrete reduced-identity-component construction.
- citations.json: full verbatim statements for every node used in every numbered proof step.

All node files are in dag/nodes/sec-six-functors-basics/ in this sandbox. Three new nodes, zero Mathlib leaves. The three new nodes carry statements only, empty proofs and proof dependencies. Search output files and searches.jsonl preserve the actual searches; search_specs.json and write_split.py record the queries and construction. No Lean was written and no compiler, Lake, local preflight or local DAG checker was run.

## Attachments

None. Searched the live lean/WeilConjectures source by the item id, multiplicative-isogeny spellings, Picard/isogeny combinations, Borel subgroup and projective-representation terminology. The project has group-scheme/isogeny definitions and abelian-variety isogenies but no declaration proving this item or the new inputs. Its existing Picard material concerns curves, descent and cohomology.

## WANTED

None. The actual local source used throughout is literature/milne-algebraic-groups_iAG2017.pdf. No prohibited SGA route is used. These algebraic-group results are sourced by their Milne proposition labels; they are not Stacks results to which an unrelated tag should be assigned.

## Problems found and corrected

The imported item has no proof; its statement correctly matches Proposition 18.22 under the algebraically closed-field hypothesis. I retained that statement and its statement dependencies. The existing inputs are lem-sfb-borel-characteristic-picard-sequence, lem-sfb-character-picard-isogeny-sequence and lem-sfb-multiplicative-isogeny-composition; I opened their complete statements and used their Borel existence and Picard surjection, final isogeny Picard surjection, and composition conclusion respectively. The first dry run passed, but a renewed shared-DAG search then found Q63's newly landed Borel-characteristic sequence. I removed my redundant Borel-surjection node and replaced its citation by that existing node. This also avoids making a separate smooth/proper quotient statement that the actual argument does not need.

Milne's instruction to pull back SL(V) to G suppresses a necessary smooth-connected replacement in the scheme setting. For a trivial projective representation the raw fibre product is G times mu_n: it is nonreduced when the characteristic divides n, and disconnected when n is prime to the characteristic and n>1. Therefore it cannot simply be called a connected group variety. The new lift statement specifies H=(E_red)^circ. The original item's assertion remains valid and unchanged. Proposition 18.6(a) explicitly uses this reduced-component repair, and 1.26, 1.38--1.39, 5.47 and Example 5.49 supply its ingredients.

The blueprint ancestry tool returns None for this item, matching its inherited blueprint.from.node=null. I preserved that null and the exact inherited chain and prepended the item in each new node's via list, rather than inventing an imported ancestor. Read the latest blueprint unit and its direct-image proof at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/. The group-theoretic work is below the inherited alteration/moduli prerequisite chain; no chapter or unit is rewritten or given a new route. The item is not its unit's key node, so no realized fields are changed.

## Unfinished work

No part of this one-level split is left unfinished. The three statement-only dependencies are deliberately left for later stage-1 splitting. Their source arguments, for that future work: effective generators arise from boundary divisors of the affine-space cell in 18.21; the projective complete-linear-system construction is the projective action implicit in 18.22 and 18.13; the lift is the pullback along SL(V) to PGL(V), followed by reduction and the identity component. The finite pullback has the dimension of G; its reduced identity component maps with finite fibres and full dimension onto connected G, and the homomorphism image theorem/5.47 gives faithful flatness. Its kernel is a closed subgroup of mu_n, hence finite diagonalizable. The second projection retains the special-linear lift. These are explanatory notes here, not proofs hidden in new-node statements.

## Not duplicates

lem-sfb-flag-effective-picard-generators vs lem-sfb-affine-space-invertible-trivial: triviality on affine space does not state existence of the affine cell of G/B or finite effective generation of the Picard group of the complete quotient.

lem-sfb-flag-projective-linear-system vs lem-sfb-homogeneous-line-bundle-sections: that node starts from a character of a Borel in a reductive group and an already homogeneous line bundle; ours starts with any effective line bundle on G/B, including a line that need not admit a G-linearization, and constructs its projective representation.

lem-sfb-flag-projective-linear-system vs lem-sfb-projective-frames-pgl: frames and automorphisms of an existing projective bundle do not give invariance or global generation of a line bundle on G/B, or the induced algebraic projective action.

lem-sfb-projective-representation-smooth-lift vs lem-sfb-semisimple-multiplicative-universal-cover: the new lemma starts with a projective representation of an arbitrary smooth connected affine group and constructs a lift to SL; the existing node assumes semisimplicity and constructs a simply connected universal cover, and depends on this item, so would be circular here.

lem-sfb-projective-representation-smooth-lift vs lem-sfb-picard-trivial-multiplicative-cover: the new lemma neither mentions nor kills Picard groups. It lifts just one projective representation. The item uses different such representations in a finite induction and then Picard surjectivity.

DAG searches covered the Milne labels 18.15, 18.21, 18.22, 18.12--18.13 and the Borel, Picard, homogeneous line, projective representation, SL/PGL and reduced-component notions across all chapters. Whole-blueprint searches used Picard, homogeneous, Borel, projective representation, multiplicative isogeny and the more specific conjunctions Picard/Borel, Picard/generator, linear/system, special/linear/cover. No existing node states any of the three retained new dependencies. The initial Borel-surjection dependency was removed when the new existing Borel-characteristic sequence was found. The general abstract algebraic-group homomorphism-factorization node is useful for splitting the lift later, but does not give its smooth multiplicative cover and representation.

## Review by Q112

I read Milne 18.22 on printed pp.392--393 together with 18.21, 18.12--18.16, 18.18, 18.2, Example 5.49, 1.26, 1.38--1.39, and the reduced identity-component argument in 18.6(a). The source is about affine algebraic groups throughout, and its split connected standing assumption holds over the algebraically closed F. I checked that the theorem does not require reductivity, semisimplicity, characteristic zero or a reduced finite kernel. That rules out using the existing reductive Borel-structure node as a black box for arbitrary G.

For step 1 I read the existing lem-sfb-borel-characteristic-picard-sequence statement and the new effective-generators statement: the former explicitly supplies an actual Borel, a represented quotient, and surjectivity of the Picard pullback as the final map in its exact sequence; the latter supplies a finite generating list with nonzero sections. Both assume exactly smooth connected affine finite type over algebraically closed F. Integer linear combinations and surjectivity give the claimed generators on G directly.

For step 2 the cited linear-system statement explicitly supplies finite nonzero V, the algebraic homomorphism to PGL, equivariant t, the tautological pullback isomorphism and its GL-linearization. It is not an invocation of the definition of homogeneous bundles or merely an abstract action on F-points. These are precisely the conclusions carried forward.

For step 3 I checked the lift's hypotheses for every composite a_i f_(i-1). Its statement explicitly makes the new source smooth and connected and its projection faithfully flat with a finite diagonalizable scheme-theoretic kernel. The composition node explicitly applies to three smooth connected affine groups and gives the multiplicativity of the composite. The induction includes the identity as stage zero; it makes no assertion about smoothness of a raw fibre product.

For step 4 the same linear-system statement explicitly includes the linear action on O(1). The two displayed fibre formulas are regular inverse maps, not just bijections on closed points: they use rho_i and its inverse as scheme morphisms and apply functorially to all scalar extensions. Thus the line becomes trivial on the group itself without needing a new Borel subgroup, identification of two flag varieties, descent, or a character-classification theorem. Previously trivialized generators stay trivial under pullback. This step is elementary from the retained data, not a new theorem about Picard groups or linearizations.

For step 5 I opened lem-sfb-character-picard-isogeny-sequence: its statement ends in Pic(G_0) to Pic(G_1) to 0 and explicitly says this arrow is pullback. Taking G_0=G and G_1=P is legitimate by step 3. Surjectivity together with the explicitly proved zero map gives Pic(P)=0.

I tested the small cases G=1, G a split torus or a connected unipotent group (G/B a point, with an empty generating family possible), a trivial line bundle (V one-dimensional), and a trivial projective representation with n divisible by the characteristic. In the last case taking reduction is necessary; the lift statement allows it. I also checked n=1 gives trivial mu_1 and no obstruction. In a semisimple adjoint example PGL_n the intended kernel mu_n can remain nonreduced, so no step replaces kernels by groups of rational points.

I read every actual Mathlib search result, including the alternate phrasings. Ring Picard functoriality and triviality for semilocal rings do not imply Borel quotient statements. Projectivization actions start from linear actions, and projective objects of Rep have a different meaning. The local Mathlib ProjectiveSpecialLinearGroup file defines an abstract quotient of groups of matrices; it does not establish the group-scheme reduced-component lift or its nonreduced kernel. Hence none of these nodes qualifies as a Mathlib leaf. All recorded queries are preserved exactly as run through msearch.py, with outputs, not inferred searches.

Finally I checked delivery-errors B--E against the actual files: standalone hypotheses and definitions for every new statement; no proof in a statement-only node; no new node is a clause of Picard-trivial covering; every non-elementary fact used by the item is a cited statement; complete literal quotes in citations.json; no citation of a proof rather than its statement; no circular use of the simply connected cover; no unit-route replacement. Every proof step is shorter than 2000 characters. No off-unit proof tool is used. The source's suppressed smoothness issue is documented above; the item's statement needs no correction.
