# Stage-1 delivery: lem-sfb-field-maximal-split-tori-conjugacy

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-field-maximal-split-tori-conjugacy.json: item, split in four steps; its statement and six statement dependencies are unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-field-parabolic-isotropy-criterion.json: statement-only, unsplit; no Mathlib match. A noncentral split torus gives a proper minimal rational parabolic.
- dag/nodes/sec-six-functors-basics/lem-sfb-field-parabolic-quotient-rational-lift.json: statement-only, unsplit; no Mathlib match. Quotient torsor, left action, identity fibre and rational lifting for an arbitrary-field parabolic.
- dag/nodes/sec-six-functors-basics/lem-sfb-split-torus-rational-fixed-point.json: statement-only, unsplit; no Mathlib match. A split torus acting on a proper scheme with a rational point has a rational scheme-theoretic fixed point.
- dag/nodes/sec-six-functors-basics/lem-sfb-minimal-parabolic-split-centralizers.json: statement-only, unsplit; no Mathlib match. Reductive Levi centralizers in a minimal rational parabolic and conjugacy of these centralizers by a rational unipotent element.
- citations.json: nine verbatim statement excerpts, covering every use in all four steps.
- searches.jsonl: genuine wrapper-generated search log. write_split.py is sandbox-only generation material, not a repository or launcher modification.

There are four new nodes and zero Mathlib leaves. No unit or chapter file is changed. No Lean was written, no compiler was run, and no git command was run in the shared read clone.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, maximal split tori, split-torus conjugacy, parabolics and reductivity. The only loosely related project hits concern split torsors and reductive Lie algebras. No declaration states the item, even before testing for sorry dependencies.

## WANTED

WANTED: J. S. Milne, Algebraic Groups, author errata web page, entry “p.545 et seq.”, for archival alongside lem-sfb-minimal-parabolic-split-centralizers. I read the author's page at https://www.jmilne.org/math/Books/iagerrata.html. The local 2017 book is present and supplies the theorem; the online page independently confirms the missing minimality hypothesis. No additional document is needed to understand the argument below.

## Source error

The item itself is true and is not STATEMENT-DISPUTED; no statement correction is needed. Two errors/omissions in its printed proof must not be propagated.

1. In the proof of Theorem 25.10, a nontrivial split torus is said to give a proper parabolic by Proposition 25.2. The proposition actually requires a noncentral split torus. For G=G_m, a nontrivial split torus exists but there is no proper parabolic. I handle the case where all split tori are central by multiplying the two tori, applying the already-existing faithfully flat image and split quotient results, then maximality. Only the complementary case invokes 25.2.
2. Theorem 25.6(b) as printed for an arbitrary parabolic is false. For G=GL_2, P=G, and the diagonal maximal split torus S, C_G(S)=S whereas R_u(P)=1, so P is not R_u(P) semidirect C_G(S). The author's published errata explicitly requires P minimal in (b). The printed version of (c), if applied for P=G, would also wrongly force all maximal split torus centralizers equal because R_u(G)=1. The new node assumes P minimal throughout and asks only for existence of the unipotent conjugator. The proof chooses a proper minimal rational parabolic before using it.

After conjugating centralizers, the two conjugated tori commute. Their product is a split torus, so their maximality already proves equality. This closes the printed proof directly, without its dimension-induction sentence or any claim that an arbitrary maximal split torus is a geometric maximal torus.

## Searches and blueprint route

I read SETUP's three levels, GOAL, the chapter and unit records, and the current latest blueprint files for the chapter and sk-thm-sf-ctf-stability, including det-thm-sf-ctf-stability-direct-images proof (3). This item is a supporting field-group input far below that proof's direct-image route. I retained its inherited blueprint.from.place and via chain. The required ancestor tool returns None for this inherited chain; children extend the via chain and preserve that null ancestor, as existing supporting nodes do. I did not invent a different ancestor or edit the unit's route.

Whole-DAG statement searches included maximal split, noncentral split, minimal parabolic, parabolic quotient, split solvable, rational fixed points, 25.2, 25.6, 25.9 and 16.51, as well as torus products and homomorphism images. Whole-blueprint searches using tools/blueprint_refs.py included parabolic, minimal parabolic, parabolic containment, parabolic quotient, proper parabolic, noncentral split, split torus, split solvable, maximal split, rational fixed, fixed point, complete algebraic, Levi and centralizer. No blueprint node states any of the four inputs. The fixed-point search returned Frobenius/local-term statements, which concern different objects.

For the item and each proposed child I ran leanfinder, loogle, grep and leansearch through msearch.py, and a second semantic phrasing. The exact query strings and raw summary records are copied from searches.jsonl into the appropriate node's mathlib_searches. All services answered successfully. I inspected the returned types: Matrix.IsParabolic describes a single 2 by 2 matrix with zero discriminant, GroupExtension.IsConj describes splittings of abstract group extensions, Subgroup.centralizer is an abstract subgroup, and the Lie/Geck declarations are about Lie subalgebras and root pairings. None is a one-line specialization giving an algebraic-group scheme statement. I also read the indicated source of Matrix.IsParabolic (Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/FinTwo.lean:40), GroupExtension.IsConj (Mathlib/GroupTheory/GroupExtension/Defs.lean:317), and Subgroup.centralizer (Mathlib/GroupTheory/Subgroup/Centralizer.lean:30). These are rejected candidates, not leaves.

## Not duplicates

lem-sfb-field-parabolic-isotropy-criterion vs lem-sfb-standard-parabolic-levi-charts: the latter treats standard parabolics of an algebraically closed semisimple group with a chosen root datum; the new node finds a rational minimal proper parabolic over an arbitrary field from noncentral split isotropy. No root data or split ambient group is assumed.

lem-sfb-field-parabolic-isotropy-criterion vs lem-sfb-minimal-parabolic-flag-projection: the latter's “minimal parabolic” is a rank-one parabolic above a Borel over an algebraically closed field. The new node's minimality is inclusion-minimal among all rational parabolics, which is a different notion.

lem-sfb-field-parabolic-quotient-rational-lift vs lem-sfb-homogeneous-orbit-quotient-geometry: the old node assumes the field algebraically closed. The new one proves rational-point surjectivity for a parabolic over finite and imperfect fields too; geometric point lifting cannot supply this.

lem-sfb-field-parabolic-quotient-rational-lift vs lem-sfb-standard-parabolic-levi-charts: the old node has algebraically closed semisimple root-data hypotheses; the new node applies to an arbitrary rational parabolic of an arbitrary reductive group over any field.

lem-sfb-split-torus-rational-fixed-point vs lem-sfb-proper-homogeneous-torus-fixed-bound: the old node assumes an algebraically closed field and homogeneous quotient; the new one is an arbitrary-field rational fixed-point existence result for any proper finite-type scheme having a rational point. A geometric fixed point is insufficient.

lem-sfb-minimal-parabolic-split-centralizers vs lem-sfb-torus-centralizer-smooth-connected: the old node gives smoothness and connectedness, with no reductivity, containment in a minimal rational parabolic, Levi decomposition or rational unipotent conjugator. It cannot justify step 4.

lem-sfb-minimal-parabolic-split-centralizers vs lem-sfb-standard-parabolic-levi-charts: the old node constructs one root-data Levi over an algebraically closed field, without comparing the two arbitrary-field maximal split torus centralizers.

lem-sfb-minimal-parabolic-split-centralizers vs lem-sfb-field-maximal-split-tori-conjugacy: the new statement compares centralizers only inside a prescribed minimal rational parabolic, and constructs the conjugator in its unipotent radical. It does not state that the original two arbitrary maximal split tori in G are conjugate; the fixed-point, rational-lifting and commuting-product arguments in the item establish that conclusion.

No new node cites a Stacks tag, so there are no same-Stacks-tag pairs to disambiguate. The source here is Milne's field-group theory, with theorem numbers and printed pages. Existing arbitrary-field flat-image and split-torus flat-quotient nodes were reused instead of duplicating them.

## Review by Q47

I read the local Milne book, Theorem 25.10 and Proposition 25.2/Theorems 25.6 and 25.9 on printed pp.545–546, and Theorem 16.51 on p.343. For the quotient child I additionally read Theorem 5.28 and Corollary 5.27 on pp.104–105: quotient representability, homogeneous action and the torsor identity. For the isotropy child I checked the cocharacter parabolic statement 25.1 and the actual noncentral condition in 25.2; the minimal proper parabolic can be chosen with least dimension among the proper rational parabolics supplied by 25.2. Strict containment of smooth geometrically connected parabolics lowers dimension, so that choice is inclusion-minimal. The source's centralizer child is read with the author-confirmed minimality correction. I tested G=1, G=G_m, split GL_2 with its upper triangular Borel, and an anisotropic group with split center. None requires a proper parabolic in the central-only case. Over a finite field no density of rational points is used: rational lifting is the full 25.9(b), including its Lang-theorem case. Over imperfect fields every torus remains k-split and every subgroup is scheme-theoretic; nothing identifies rational-point images with subgroup-scheme images.

For step 1 I opened the existing coordinate-torus node, affine-homomorphism-flat-image node and field-split-torus-flat-quotient node and read their complete statements. The first explicitly supplies finite type for a coordinate split torus over any field; the second factors any finite-type affine group homomorphism through a closed faithfully flat image without smoothness or perfectness assumptions; the third says precisely that such a faithfully flat quotient of a split torus is split, retaining possibly inseparable kernels. Multiplication is a homomorphism because the two subgroups commute. Its restrictions to the factors prove that the image contains both subgroups, so maximality applies. This is a short assembly from cited facts, not a new “commuting tori conjugacy” node. Rank zero is allowed in all three cited inputs.

For step 2 the isotropy child's statement supplies a proper minimal P only in the noncentral case; its explicit definition of parabolic supplies proper finite-type G/P. The quotient child supplies the action, quotient morphism and identity fibre. The all-central case invokes the completed step 1, so the invalid nontrivial-to-noncentral inference in the book is absent. This also handles unequal proposed ranks: maximality forces the common product torus to equal both.

For step 3 the fixed-point child requires X(k) nonempty, not just geometric nonemptiness. The quotient's identity coset supplies that point. Its conclusion is fixedness on all algebra points, and the rational-lift child's statement supplies h_i over k. I checked the inverse order explicitly: a fixed coset h_i P gives h_i^{-1} S_i h_i inside P. Equivariance and the torsor identity fibre prove that containment after every algebra extension. Testing the universal S_i point gives factorization of the morphism, rather than merely containment of underlying topological images. Conjugation preserves the split-torus property and maximality, and maximality in G implies maximality in P.

For step 4 the minimal-parabolic-centralizers child has exactly the hypotheses now established and returns a rational u conjugating L_1 to L_2. Its centralizer definition quantifies over all further algebra extensions. Because R_1 is commutative it lies in its centralizer; after conjugation the first torus therefore commutes with R_2. Step 1 finishes. I checked the final order g=h_2 u h_1^{-1} by substitution and read def-sc-group-scheme for the inverse and composition group identities. This is an isomorphism of group schemes, not just equality on rational points. The citations.json quotations were checked as verbatim substrings of the cited statements, with each cited result used only for what its statement supplies.

Against delivery-errors B–E: each new node is self-contained and statement-only (B1–B3), its TeX and exact logged searches are preserved (B4,B7), the source is Milne rather than a misleading Stacks tag (B5), and there are no claimed Mathlib matches (B6,B8). Blueprint ancestry and exact-project-declaration checks are recorded above (B9,B10). Every non-elementary fact has a cited statement (C1–C4); searches and duplicate comparisons are recorded (C5). No child depends on the item or on its rational-containment parent, so no cycle is introduced (C6). The coordinate-torus finite-type fact from the trace-formula unit is declared in split_report.tool_uses as a field-independent tool (C7,C8). The four new nodes are distinct prerequisites, not clauses relabelled as the original conclusion, and the proof includes the conjugation and product arguments (D1–D5). All hypotheses, the quotient object and inverse order, inseparable kernels, finite fields, improper parabolic counterexample and trivial groups were checked as above (E1–E6); the two source omissions are explicitly repaired (E7). Every step is below 2000 characters; no long step hides an unsplit comparison.

The preliminary server check_dag found combined bracket references accidentally stored as single dependency IDs in the new-node generator. I corrected stmt_deps parsing to separate individual IDs. This was a serialization error, not a change in mathematics. The independent server review_split already passed the item; final deliver.py --no-push will validate the complete delivery tree and all new nodes.

## Unfinished work

None at the requested one-level split: the four children intentionally remain statement-only for their future stage-1 items. No attachment, compiler, stage-2 statement or stage-3 proof is claimed.
