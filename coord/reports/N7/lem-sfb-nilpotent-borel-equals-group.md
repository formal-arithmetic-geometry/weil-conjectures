# Stage-1 delivery: lem-sfb-nilpotent-borel-equals-group

Group N7, 2026-10-24. Direct delivery; no second worker and no agents started.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nilpotent-borel-equals-group.json: statement, split; no Mathlib match. Original statement, source, statement dependencies, blueprint provenance and previous searches retained. Five proof steps replace the empty proof.
- dag/nodes/sec-six-functors-basics/lem-sfb-borel-homomorphism-rigidity.json: statement, unsplit; no Mathlib match. The sole new node is Milne Proposition 17.21, including arbitrary coefficient algebra R.
- citations.json: a verbatim quotation from the statement of each node cited by each numbered step.
- report.md: this report. searches.jsonl is the search command's unedited log.

## Attachments

None. Searched lean/WeilConjectures both for the exact blueprint id and for Borel/borel and nilpotent group wording. No declaration states the item or the new rigidity theorem. Existing sorry declarations would not have qualified. No Lean file was written and no compiler, Lake or build tool was run.

## Literature

WANTED: none. Read the available literature/milne-algebraic-groups_iAG2017.pdf, printed pp.357--359: Proposition 17.20, Proposition 17.21 and its complete proof over arbitrary R, Proposition 17.22, and the implication (b) to (c) of Proposition 17.23. Also inspected Corollary 6.40, p.134, to understand the source's dimension induction. For the proper-affine leaf read literature/stacks-project/morphisms.tex, Tag 01WN, label lemma-finite-proper, including its statement and proof.

## Corrections and route

There is no statement dispute and no statement change. The item was statement-only. Its meaning agrees with Milne 17.23 under the algebraically closed, smooth connected affine finite-type conventions of Chapter 17b. The proof follows Milne's central-quotient argument, with induction indexed by the supplied central-series length rather than the dimension of B. The last term N=B_(m-1) is central in B. Milne 17.21 makes it central in G, even when N is nonsmooth or disconnected, so the quotient reduces that series length by one. This avoids silently assuming smoothness of Z(B) or of the original series terms. The unchanged unit and chapter route are respected: read latest sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md (3), and the DAG unit and chapter records. The inherited blueprint ancestor command prints None; the existing null from.node and complete supporting chain were retained, with precise additional place and via for the new node.

The new rigidity theorem is a general comparison of two homomorphisms after arbitrary algebra base change. It is neither the equality B=G nor a clause of the item's conclusion. Its own proof is deliberately not included in the new unsplit node. Milne's proof descends the difference map to the proper flag quotient, uses constant global functions and scalar extension, and then affineness of the target; this explains why rigidity is a substantial prerequisite rather than an elementary assertion.

## Searches and reuse

Before creating the new node searched the whole DAG by Borel, centralizer, centre, rigidity, agreement of homomorphisms and the literal source references 17.21/17.22, and read the statements of the plausible candidates. Searched the entire imported blueprint using tools/blueprint_refs.py search nilpotent, 'Borel homomorphisms', 'proper affine', and Borel. Its nilpotent hits concern Lie algebras, affine varieties or nilpotent ideals; none asserts this algebraic-group theorem. The proper-affine blueprint result is restricted to curves, so reused the existing general Mathlib leaf lem-sc-proper-affine-finite-general. Reused the existing affine-normal-quotient-geometry, quotient-borel-torus-images and borel-quotient-proper-geometry nodes after reading their full statements. Did not create a centre representability, quotient nilpotence, trivial-group base case, or inverse-image node: the existing quotient statement and explicit elementary arguments suffice.

Ran the required msearch.py commands for both the item and new node. For the new node the exact logged queries cover leansearch, loogle, grep restricted to AlgebraicGeometry, whole-Mathlib grep, and two distinct leanfinder formulations. Every service answered successfully. LeanSearch returned abstract GrpCat/profinite hom extensionality, which requires agreement on the whole group. LeanFinder returned affine/global-section extensionality, dense-open extensionality, matrix inclusion injectivity, and abstract-group solvability; none detects agreement on a Borel subgroup. Read Mathlib/AlgebraicGeometry/AffineScheme.lean:154 (ext_of_isAffine), AlgebraicGeometry/Morphisms/FormallyUnramified.lean:193 (infinitesimal thickening uniqueness), and Algebra/Category/Grp/Basic.lean:151. These cannot specialize in one line to the new result. AlgebraicGeometry grep found no Borel theorem; whole-Mathlib Borel hits concern measurable spaces. Item searches returned abstract nilpotent-group and Cartan/Lie-algebra statements, not a scheme-theoretic Borel theorem. Existing recorded item searches were preserved, including its previous second phrasing. No unavailable result was recorded as a no-match and no unrun search was added.

## Not duplicates

lem-sfb-borel-homomorphism-rigidity vs lem-sfb-isogeny-torus-conjugacy: the existing node gives conjugacy by a torus element for reductive finite-kernel surjections agreeing on characters of a maximal torus; it does not state equality from Borel restriction or allow arbitrary algebra-base-change homomorphisms.
lem-sfb-borel-homomorphism-rigidity vs lem-sfb-isogeny-simple-root-rigidity: the existing node requires reductivity, two finite-kernel surjections, agreement on a maximal torus and on the simple positive root groups; the new node treats arbitrary homomorphisms of connected affine groups after arbitrary algebra base change from equality on the whole Borel.
lem-sfb-borel-homomorphism-rigidity vs lem-sfb-borel-scheme-normalizer: normalizer equality concerns the subgroup functor of elements preserving B; it does not imply equality of two homomorphisms agreeing on B. No use is made of its proof.

## Review by N7

I read the item against Milne 17.23(b) implies (c), and the new statement against the entire Proposition 17.21 on printed p.358. Both have smooth connected affine finite-type groups over an algebraically closed field. The new node explicitly quantifies over all commutative R and requires equality as scheme morphisms on B_R, exactly what the inner-automorphism application needs. It does not replace equality on nonreduced algebras by equality on k-points.

For step 1, I checked the hypotheses and all clauses of lem-sfb-borel-quotient-proper-geometry. With B=1, the identity G->G really is the required represented homogeneous quotient. The node says G and X are integral and that maximal solvability of H makes X proper. The separate statement of lem-sc-proper-affine-finite-general supplies finiteness with no curve or dimension hypothesis. The remaining finite-dimensional-domain argument proves C=k directly. Nonemptiness comes from the identity section.

For step 2, the given commutator property at i=m-1 holds after every algebra extension, so Int(n) is literally the identity on B_R, not just on its rational points. The new rigidity statement applies with target G_R, with no surjectivity, reductivity or separability requirements. It then gives centrality and normality of N on every test algebra. This writes the part of Milne 17.22 needed here out from 17.21, rather than creating a separate elementary centre-inclusion node.

For step 3, I checked the full statement of affine-normal-quotient-geometry: it represents the quotient by any closed normal N, not just smooth N, gives its kernel, faithfully flat finite presentation, preservation of smoothness and geometric connectedness, and the subgroup correspondence. The base is already algebraically closed, so the geometric-connectedness convention in that node holds. Quotient-borel-torus-images states precisely that the Borel image is Borel and the restricted map is faithfully flat, with no restriction on the kernel. No maximal-torus clause is used.

For step 4, I checked the actual correspondence clause, not a construction in the cited proof. Each original B_i contains N and therefore is the inverse image of a closed D_i. The maps B_i->D_i are the base changes of q. Two sections lift over a common fppf cover, the commutator identity is functorial, and membership in a closed subscheme descends because its defining ideal vanishes faithfully flat locally. This is the elementary quotient-series calculation from the cited quotient statement; it asserts no uncited general nilpotence theorem. The last image is 1 because N is the scheme-theoretic kernel. Neither smoothness of the B_i nor surjectivity on A-points is used.

For step 5, all hypotheses of the induction for (Q,D) were established before it was invoked, and the new length is strictly m-1. The same quoted subgroup correspondence says q^{-1}(D)=B. Pulling back D=Q concludes scheme-theoretic equality, not just equality of underlying sets. The base, decreasing parameter and inductive conclusion are explicit and there is no dependency cycle.

I tested m=0 and m=1, repeated trivial final terms in a nonminimal series, the trivial group, tori, G_a, and upper unitriangular groups (including the two-step Heisenberg example). An arbitrary dual-number coefficient algebra does not affect the commutator identities or fppf descent. The new rigidity theorem is tautological for B=G and for a trivial source/target; SL_2 with its standard Borel is the substantive proper-Borel case covered by the source. Dropping connectedness would fail for a nontrivial finite constant group with trivial Borel; dropping smoothness would fail for mu_p in characteristic p with trivial smooth Borel, so both hypotheses were retained. All new statements are self-contained, all notion references are statement dependencies, and the new node has empty proof and proof_deps. I checked delivery-errors B through E against the files and the sources: there is no hollow definition, invented search, hidden source lemma, clause relabelling, extra hypothesis or altered conclusion. Every step is below 2000 characters. The proper-affine Mathlib leaf is a generic tool from its other unit; all other proof dependencies are in this item's unit. No SGA source is cited.

## Unfinished work

No stage-1 argument is left unfinished. The new statement-only rigidity prerequisite remains unsplit for its own future item, as required by a one-level split. This delivery awaits the required server dry run and push; their final outcomes will be appended below.
