# Stage-1 report: lem-sfb-local-square-zero-small-extension-reduction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-local-square-zero-small-extension-reduction.json: statement; split, with statement and statement dependencies unchanged. Six proof steps, two existing proof dependencies. The recorded searches do not find the item in Mathlib.
- citations.json: verbatim statements backing every proof-step citation.
- report.md: this report. searches.jsonl contains the actual msearch runs. The sandbox also contains the local write_split.py used to write the JSON; it is not a DAG delivery file.

No new node is created; zero new Mathlib leaves. The existing Mathlib leaves reused are lem-weil-pbc-noetherian-local-quotient-artinian-local and lem-trf-vector-subspace-complement.

## Attachments

None. Searched the whole project WeilConjectures source by the blueprint tag and by small extension, square-zero lifting, nilpotent maximal ideal and related names. The ArtinianLiftingFiniteKernel and ArtinianLiftingTruncatedSection results concern Artinian targets and different lifting hypotheses. SmoothAtPrimeArtinianLiftingReverse requires a finite-type map from a Noetherian base. None states this item, which assumes only that S is Noetherian and allows non-Artinian test rings. No compiler, Lake or Lean-writing tool was run.

## WANTED

None. Read literature/stacks-project/more-algebra.tex, Tag 0DYG, lemma-fs-local, its statement and complete proof (especially the last paragraph, (3) implies (2)); and algebra.tex, Tag 02HS, definition-small-extension. For the two reused leaves I read their complete node statements and Mathlib/LinearAlgebra/Basis/VectorSpace.lean, Submodule.exists_isCompl at lines 280--282. The Artinian quotient statement has precisely the power-containment hypotheses used here.

## Corrections and route

No statement dispute or statement change. The input had no proof. The essential pitfall is that A and J can be infinite: neither A nor the inverse-image subring C is assumed Artinian. Only D=C/J, a quotient of S by an ideal containing a maximal-ideal power, and the codimension-one quotients C/H are proved Artinian. The product is indexed by the set of subspaces of J; no finite-dimensionality or small-index-category existence theorem is required.

Read AGENTS.md, the worker role and brief, stages/1-dag.md, the three SETUP levels, GOAL.md, the chapter and unit records, the latest blueprint direct-images proof and unit, and delivery-errors B--E. The current latest direct-images proof uses compactification, whereas the inherited supporting ancestry records alteration/deformation input. I retain that ancestry and the assigned algebraic source; I change no unit route. blueprint_refs ancestor returns None, agreeing with the inherited null from.node. Whole-blueprint searches for 0DYG, small extension, Artinian, square-zero, square zero lifting, hyperplane, retraction, complement and Noetherian local, together with DAG tag/concept searches, locate no replacement for the item. No new nodes are introduced. The existing trace-formula complement node is general linear algebra, a Mathlib leaf, so it is available as a tool independently of its unit.

## Unfinished work

None in this one-level split. The delivery still requires the maintainer's independent content review. The two proof dependencies are already Mathlib leaves.

## Review by N8

I checked the source's filtration and product argument directly against the written six steps. In step 1, K_t=m_A^t J ends at zero because m_A^N=0, not because J is finite. Every successive kernel is square zero and killed by the maximal ideal. The lift stays local and retains the residue isomorphism because quotienting by a nilpotent ideal reflects units. Thus induction really reduces the original test to the socle-kernel case, rather than applying the small-extension hypothesis directly to an infinite kernel.

Step 2 uses exactly the statement of lem-weil-pbc-noetherian-local-quotient-artinian-local, with its ring C replaced by S and its ideal K replaced by ker(S->v(S)). I verified n^N is contained in this kernel, the kernel is contained in n, N is positive, and S is Noetherian. The residue of v(S) is all of k because the given residue map is an isomorphism. The explicit inverse b(1-j) proves locality of the inverse-image subring, including its local R-structure. Inclusion into A proves its nilpotence bound and socle annihilation. No unproved theorem about arbitrary subrings being local or Noetherian is used.

Step 3 cites lem-trf-vector-subspace-complement, whose statement explicitly allows arbitrary-dimensional V. Apply it to kj in J to find a hyperplane avoiding each nonzero j. The scalar action factors through C/m_C because m_C J=0, so these subspaces really are C-ideals. This proves separation without silently treating an infinite vector space as finite.

Step 4 uses no external result: I wrote out the descending-chain proof for C/H. The chain of images in D stabilizes by step 2; its intersections with J/H stabilize because a one-dimensional space has only two subspaces. Equal images and intersections force equality for nested ideals by the displayed x-y argument. Hence these rings are Artinian, local with residue k, and their nonzero kernels satisfy the exact small-extension definition. The local R-map and residue-isomorphism hypotheses for the assumed lifting test are checked. Choosing all the individual lifts uses ordinary classical choice.

Step 5 is the coordinate construction of the common-image subring of the product. I verified its common-image map is defined (the index set is nonempty), that C maps into it, that its kernel is the full product of J/H, and that C embeds: vanishing in every coordinate puts an element into the intersection in step 3. Products and scalar actions are coordinatewise, so the common residue acts on the kernel and its square is zero. The chosen lifts have the same reduction and structural R-map, so they give an R-algebra map into this ring.

Step 6 uses precisely the arbitrary-subspace complement statement a second time, now for i(J) in the product kernel. The complement M is an ideal because the action factors through the residue field. I checked existence and uniqueness of e=i(c)+m, then additivity, multiplicativity, the unit and the R-structure of the projection rho. Thus the source's shorthand direct-sum assertion supplies an actual ring retraction, not merely an additive projection. Its composition with the tuple of lifts reduces to the desired S->D and then to the original v. Step 1's finite induction now finishes the general case.

Against B--E: the unchanged statement introduces all rings and lifting hypotheses and defines local, Artinian and small extension inline; Noetherian has its correct definition dependency. There are no statement-only new nodes to audit, no duplicate or new clause restating the item, no hidden non-elementary uncited lemma, no citations of another node's proof instead of statement, and no cycle through a parent smoothness criterion. Each cited statement was opened and copied verbatim into citations.json. The two steps containing the real general facts cite their nodes; the other steps are explicit elementary calculations or an application of the item's hypothesis. All steps are under 2000 characters. No SGA source is used.

Edge cases checked: J=0 uses the quotient inverse; N=1 has A a field and J=0; repeated equal terms in the m_A^t J filtration are identity maps. For dim_k J=1 there is the hyperplane H=0 and the product retraction becomes the identity. For infinite-dimensional J, the family is still a set, each one-dimensional quotient is Artinian by the same chain argument, and the complement leaf has no finiteness assumption. The construction also works in mixed characteristic, since only the socle ideals, not the whole rings, are treated as k-vector spaces. A=k plus an infinite square-zero vector space is an allowed non-Artinian test and is handled by the same product argument. No hypothesis on the Noetherianity of R or the Artinianity of A has been introduced.

## Dry-run repair

The first server preflight rejected the phrase "the item's" in proof step 4 under its self-contained-statement wording check. Replaced it with "as defined in the statement"; the mathematical argument and hypotheses are unchanged.
