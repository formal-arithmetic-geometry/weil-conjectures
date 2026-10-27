# Repair report: lem-sfb-plane-hypersurface-cohomology

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-plane-hypersurface-cohomology.json: unchanged statement, four-step split assembly.
- dag/nodes/sec-six-functors-basics/lem-sfb-projective-hypersurface-structure-sequence.json: statement, unsplit, no Mathlib match; assigned returned steps 1--3.
- dag/nodes/sec-six-functors-basics/lem-sfb-closed-immersion-cokernel-cohomology.json: statement, unsplit, no Mathlib match; assigned returned steps 4 and 6.
- citations.json: one verbatim statement quote for each step/node pair. searches.jsonl contains the actual Q52 search records. returned-proof.json preserves the seven returned steps; repair.py regenerates this delivery.

## Attachments

None. Searched lean/WeilConjectures by the item blueprint tag and by plane/hypersurface/cohomology concepts. The actual library declaration AlgebraicGeometry.PlaneHypersurface.cohomology_of_nonzero_homogeneous in lean/Sheaf/AlgebraicGeometry/PlaneHypersurfaceCohomology.lean still has sorry. Its construction and hypotheses agree with the DAG. ClosedImmersionRankedCohomologyReconstruction is about reconstructing exterior complexes with prescribed homology, not these global cohomology maps. No Lean was written and no compiler or build tool was run.

## WANTED

None. All mathematical sources for this repair are present locally.

## What was wrong and what changed

The return concerns work distribution, not the statement: the old seven-step proof was 5345 characters. The sandbox initially contained only .brief2--.brief5, with no nodes, report, citations or search log. I therefore continued from the current repository node, which retains the returned seven-step argument and previous review/Lean metadata. The item is not a key node of the unit, so no unit/chapter field is edited. All imported and prior metadata is retained. The blueprint ancestor command returns None; the new nodes inherit precisely this null ancestor and extend its existing via chain by the item. Blueprint searches for hypersurface, hypersurface exact sequence, closed immersion cohomology, cokernel cohomology and 0BYD found no matching blueprint statement. Searches across all DAG statements additionally inspected the existing closed-pushforward, scalar-comparison and boundary nodes listed below.

The first new node is a sheaf construction, not a clause about H0 or genus. Its proof assignment is the graded principal ideal sequence, exact sheafification, chart twist identification and quotient sheaf gluing. The second is a general geometric module-cohomology exact-sequence lemma; its proof assignment is the module/abelian comparison, scalar compatibility and actual derived-functor boundary construction. It does not assert a dimension or mention plane hypersurfaces. These are separate arguments of comparable size (2385 and 1920 returned text characters); neither restates the whole item. Their JSON files are statement-only: empty proof and proof_deps, null proof_origin, status unsplit. The remaining 1040 characters of returned steps 5 and 7 are retained in the item, with the same monomial basis and complete count. The four-step item assembly totals 2040 characters. No proof step exceeds 2000 characters.

The general abstract Mathlib CategoryTheory.ShortComplex.ShortExact.isIso_δ and δIso (Mathlib/Algebra/Homology/HomologySequence.lean:359,365) apply to already given short exact complexes. They do not construct the ringed-space resolution comparison or identify module cohomology across a closed immersion. The Proj.fromOfGlobalSections and graded chart hits construct schemes/maps, not the hypersurface sheaf sequence. All search verdicts are based on the returned types and these sources; the two rate-limited LeanSearch calls are explicitly unavailable. Each new node has two semantic phrasings, Loogle and two grep queries. Existing historical item searches are preserved, and Q52 searches are appended.

## Preserved arguments assigned to the new nodes

The following text is retained for future workers. It is deliberately in this report, not in the statement-only node files. Every original argument is reproduced here or in the item's steps.

### Structure-sequence node: returned steps 1--3

Returned step 1: Put $S=k[A,B,C]$ with its total-degree grading. By [lem-weil-pbc-polynomial-ring-domain], $S$ is a domain. Since $F\ne0$, multiplication by $F$ is injective. With the shift convention $S(-d)_m=S_{m-d}$ of [def-weil-pbc-proj-twisting-sheaf], that map is degree-preserving, its image is the homogeneous ideal $(F)$, and the quotient map is surjective with precisely this kernel. Hence $0\to S(-d)\xrightarrow{F}S\to S/(F)\to0$ is an exact sequence of graded modules.

Returned step 2: Apply [lem-sfb-proj-graded-sheafification-exact] on $P=\operatorname{Proj}(S)$ to get $0\to\widetilde{S(-d)}\xrightarrow{\widetilde F}\widetilde S\to\widetilde{S/(F)}\to0$. The sheaves $\widetilde S$ and $\widetilde{S(-d)}$ identify with $\mathcal O_P$ and $\mathcal O_P(-d)$: by [def-weil-pbc-proj-twisting-sheaf] their chart sections are respectively $(S_{x_i})_0$ and $(S_{x_i})_{-d}$, the latter freely generated by $x_i^{-d}$. Multiplication by this generator also identifies the modules on every smaller positive homogeneous basic open contained in $U_i$, and commutes with localization restrictions, so these are sheaf trivializations. On an overlap, $x_i^{-d}=(x_i/x_j)^{-d}x_j^{-d}$, exactly the transition in [def-pc-projective-space-twist]. Under these identifications $\widetilde F$ is multiplication by $F$, by the fraction formula for induced maps in [lem-sc-p1-proj-tilde-functorial].

Returned step 3: Identify $\widetilde{S/(F)}$ with $i_*\mathcal O_Z$ for the specified closed immersion $i:Z\hookrightarrow P$. On every standard basic open $U=D_+(g)$ for homogeneous $g$ of positive degree, both sheaves have sections $((S/(F))_g)_0$: for the first this is the definition in [def-weil-pbc-proj-twisting-sheaf], and for the second it is the standard-open description of $\operatorname{Proj}(S/(F))$ in [def-pc-proj]. The structure map sends a homogeneous degree-zero fraction $a/g^m$ to $\bar a/\bar g^m$. These chart maps and identifications commute with restrictions, since each restriction is the same localization of the same fraction. They therefore glue, by the sheaf axiom on the standard affine basis, to an isomorphism carrying the sheafified quotient map to the closed-immersion structure map [def-weil-closed-immersion]. Thus the sequence from step 2 is $0\to\mathcal O_P(-d)\xrightarrow{F}\mathcal O_P\to i_*\mathcal O_Z\to0$, with its actual restriction map. No radical or prime ideal is substituted for $(F)$.

### Cokernel-cohomology node: returned steps 4 and 6

Returned step 4: For every $q\geq0$, identify $H^q(P,i_*\mathcal O_Z)$ with $H^q(Z,\mathcal O_Z)$. Indeed [lem-sc-zariski-module-abelian-cohomology-agree] compares module cohomology to cohomology of the underlying abelian sheaf on both schemes, and [lem-sc-cohomology-closed-immersion-pushforward] supplies the comparison for those abelian sheaves, since $i$ is a homeomorphism onto a closed subset. Forgetting the module structure commutes with $i_*$, directly from its open-set formula. Naturality of both comparisons with respect to multiplication by each scalar of $k$ makes the resulting isomorphisms $k$-linear. In degree zero the comparison is the equality of global sections $\Gamma(P,i_*\mathcal O_Z)=\Gamma(Z,\mathcal O_Z)$, so the map induced by $\mathcal O_P\to i_*\mathcal O_Z$ is restriction of functions.

Returned step 6: Apply [lem-weil-pbc-derived-functor-long-exact] to global sections of module sheaves on $P$, valued in the abelian category of $k$-vector spaces. The category is abelian with enough injectives by [lem-sc-ringed-space-module-sheaves-enough-injectives]; global sections is additive and left exact since sections of a kernel are the kernel of the section map. The same injective resolution computes these right derived functors: its global-section complex is the complex of [def-sc-ringed-space-module-cohomology], with its induced $k$-vector-space structure. Using steps 3--5, the initial segment is $0\to0\to k\to H^0(Z,\mathcal O_Z)\to0$, and the segment around the next boundary is $0\to H^1(Z,\mathcal O_Z)\xrightarrow{\delta}H^2(P,\mathcal O_P(-d))\to0$. Thus the scalar restriction map is bijective, and the boundary is an isomorphism of $k$-vector spaces. All arrows, including the boundary, are $k$-linear because the derived-functor sequence is taken in $k$-vector spaces. The degree-zero map is a unital $k$-algebra homomorphism (restriction of functions); being bijective it is an isomorphism of $k$-algebras.

In the first assignment replace the three variables by x_0,...,x_n; nothing in the chart/domain/gluing argument depends on there being three variables. In the second assignment replace O(-d), O and O_Z by L, E and M, and substitute the four explicitly assumed vanishings for returned step 5. The cohomology map in degree zero is the specified u, so specialization back to structure sheaves gives actual restriction, not an arbitrary vector-space equivalence.

## Review by Q52

I read Stacks curves.tex, Tag 0BYD, lemma-genus-plane-curve, proof in full (the graded sequence, sheaf sequence, closed-immersion comparison and two cohomology isomorphisms). I also read constructions.tex, Tag 01M7, lemma-proj-sheaves; coherent.tex, Tag 01XT, lemma-cohomology-projective-space-over-ring; cohomology.tex, Tag 02UV, lemma-cohomology-and-closed-immersions; sites-cohomology.tex, Tag 03FD, lemma-cohomology-modules-abelian-agree; and derived.tex, Tag 015B, lemma-higher-derived-functors. These are the sources of both new proof assignments. This keeps the coherent-cohomology route of 0BYD; there is no SGA citation and no alteration-route change.

Step 1 cites the new structure-sequence statement. I checked its statement gives both exactness and the actual restriction arrow, with (F) rather than its radical. A field makes the polynomial ring a domain, F is nonzero and homogeneous, and the shift convention is S(-d)_m=S_{m-d}. Returned steps 1--3 supply the complete assigned proof: 01M7 applies to this N-graded ring with Z-graded modules; x_j^{-d} has the correct transition (x_j/x_l)^{-d}; the quotient chart maps are precisely the quotient fraction maps and commute with localization. I read every old cited statement: polynomial-ring-domain gives the domain, proj-twisting-sheaf gives the shift and localized sections, proj-graded-sheafification-exact gives exactness, projective-space-twist gives the transition, proj-tilde-functorial gives the induced fraction maps, def-pc-proj gives the quotient charts and closed-immersion defines the structure map. None is used only through its proof.

Step 2 retains the old projective-space computation and cites lem-pc-projective-space-twist-cohomology. I read its full statement: at n=2, twists -d and 0 give all four vanishings required by the new cohomology node, the canonical constants, and the exact negative Laurent monomial basis in H2. Its n=0 exception is irrelevant. No geometric hypothesis is added.

Step 3 cites the new cokernel-cohomology statement, whose displayed low-degree consequences are exactly the two linear isomorphisms used. The specified sequence is available from step 1 and all four vanishings from step 2. I read the old comparison statements: zariski-module-abelian-cohomology-agree is canonical, natural in every module morphism and the identity on H0; cohomology-closed-immersion-pushforward applies because a scheme closed immersion is a topological closed embedding and is natural for every abelian sheaf. The open-set direct-image formula commutes with forgetting module structure. Scalar multiplication is a sheaf morphism and i is over k, so these naturalities make the composite k-linear. The old enough-injectives statement supplies an abelian module category with enough injectives; derived-functor-long-exact applies to additive left exact global sections valued in k-vector spaces; ringed-space-module-cohomology defines these same cohomology groups by that global-section complex. These statements justify the second assignment without a hidden flatness, quasi-coherence or properness assumption. The parent only observes that its actual restriction map preserves products and 1, so the linear bijection of H0 is the asserted algebra isomorphism.

Step 4 is the full elementary count of the basis in step 2, using the boundary isomorphism already established in step 3. For d=1,2 the basis is empty; for d=3 it has one element; for d=4 there are three. The change e_i to a_i=-e_i-1 and the sum over a_0 give the integer triangular number, so no division in k occurs.

I tested the first new statement on F=x_0, F=x_0^2 and F=x_0 x_1: its charts give a hyperplane, a doubled hyperplane and a reducible divisor without changing the exact sequence. The excluded F=0 would destroy injectivity, explaining that hypothesis. For n=1 the same sequence remains true; its cohomology is deliberately not computed by the P2 item. For the second statement take i=id, L=0, E=M: the H0 comparison is identity and the asserted H1 boundary is an isomorphism only under the explicitly required vanishing H1(E)=0. For an empty Y its sequence forces L to E to be an isomorphism; the conditional H0 and H2 conclusions then correctly vanish. General non-quasi-coherent modules are allowed by each cited comparison and injective-resolution theorem. The parent checks F=A, A^2, ABC, A^3 in every characteristic: dimensions 0,0,1,1 and no reducedness hypothesis is needed.

B1--B10: new statements introduce all objects and notions, cite definition nodes, use single TeX escaping, are statement-only, name their correct Stacks tag/label, have faithful actual search logs, inherit blueprint fields, and have no exact finished Lean or Mathlib match. C1--C8: every non-elementary parent step has a cited statement with verbatim citations.json; assigned old uses are explained above; no new node depends on the item, so no cycle is introduced; chapter/unit route is retained and no new off-unit tool use is introduced. D1--D5: the two distinct proof arguments are distributed, not the item's two clauses or the whole conclusion, and all details are preserved above. E1--E7: hypotheses and small cases were checked as described; no false statement or source error was found and the item statement is unchanged.

## Not duplicates

lem-sfb-projective-hypersurface-structure-sequence vs lem-sfb-plane-hypersurface-cohomology: states global functions and genus, whereas the new node supplies a structural intermediate without that dimension formula.

lem-sfb-projective-hypersurface-structure-sequence vs lem-sfb-fermat-kummer-relative-curve: states finite Kummer-cover geometry for a relative Fermat curve, not this general sheaf/cohomology construction.

lem-sfb-projective-hypersurface-structure-sequence vs lem-sfb-proj-graded-sheafification-exact: states exactness of the general tilde functor, not the hypersurface quotient/twist identification or the scalar cohomology sequence.

lem-sfb-projective-hypersurface-structure-sequence vs new-picard-residue-homology-naturality-fixed-positive: states simultaneous residue-homology comparisons in a positive finite family, not this geometric sheaf/cohomology construction.

lem-sfb-projective-hypersurface-structure-sequence vs new-picard-residue-homology-geometric-naturality-fixed-per-index: states per-index residue-homology choices, not this construction.

lem-sfb-projective-hypersurface-structure-sequence vs new-picard-residue-homology-naturality-fixed: states family residue-homology naturality, not this construction.

lem-sfb-closed-immersion-cokernel-cohomology vs lem-sfb-plane-hypersurface-cohomology: states global functions and genus, whereas the new node supplies a structural intermediate without that dimension formula.

lem-sfb-closed-immersion-cokernel-cohomology vs lem-sfb-fermat-kummer-relative-curve: states finite Kummer-cover geometry for a relative Fermat curve, not this general sheaf/cohomology construction.

lem-sfb-closed-immersion-cokernel-cohomology vs lem-sfb-proj-graded-sheafification-exact: states exactness of the general tilde functor, not the hypersurface quotient/twist identification or the scalar cohomology sequence.

lem-sfb-closed-immersion-cokernel-cohomology vs new-picard-residue-homology-naturality-fixed-positive: states simultaneous residue-homology comparisons in a positive finite family, not this geometric sheaf/cohomology construction.

lem-sfb-closed-immersion-cokernel-cohomology vs new-picard-residue-homology-geometric-naturality-fixed-per-index: states per-index residue-homology choices, not this construction.

lem-sfb-closed-immersion-cokernel-cohomology vs new-picard-residue-homology-naturality-fixed: states family residue-homology naturality, not this construction.

lem-sfb-projective-hypersurface-structure-sequence vs lem-sfb-closed-immersion-cokernel-cohomology: the first constructs a projective hypersurface short exact sequence; the second compares module cohomology and boundaries for an arbitrary closed-immersion cokernel sequence.

lem-sfb-closed-immersion-cokernel-cohomology vs lem-sc-cohomology-closed-immersion-pushforward: only abelian-sheaf comparison, with no module k-actions or mixed-source long exact sequence.

lem-sfb-closed-immersion-cokernel-cohomology vs lem-sc-zariski-module-abelian-cohomology-agree: only module/abelian comparison on one scheme.

lem-sfb-closed-immersion-cokernel-cohomology vs lem-sc-closed-pushforward-boundary-naturality: starts with a whole sequence on Y and pushes it forward; here L and E are arbitrary modules on X and need not be pushed from Y.

lem-sfb-closed-immersion-cokernel-cohomology vs lem-sc-leray-closed-pushforward-cohomology: only topological abelian-sheaf comparison under higher-direct-image vanishing.

lem-sfb-closed-immersion-cokernel-cohomology vs lem-pc-m1-leray-acyclic-pushforward-linear-comparison: only linear cohomology comparison under an acyclicity hypothesis, without the mixed-source cokernel exact sequence or its actual connecting map.

lem-sfb-closed-immersion-cokernel-cohomology vs lem-weil-pbc-derived-functor-long-exact: abstract derived-functor sequence, without the geometric module/abelian comparison or k-linear direct-image identification.

## What remains

The proofs of the two new statement-only lemmas are intentionally assigned to independent later workers, as the return requires. This item has a complete assembly. Required dry-run and delivery results are recorded below after the tools finish.

## Validation

The required deliver.py --no-push exited 0 and printed OK (not pushed) at c3b3dea1763: server preflight passed, including the DAG and split checks. No local DAG/preflight checker or compiler was run.
