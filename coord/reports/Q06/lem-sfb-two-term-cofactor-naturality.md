# Stage-1 delivery: lem-sfb-two-term-cofactor-naturality

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-two-term-cofactor-naturality.json`: existing statement, unchanged; eight proof steps, status split. Twelve existing proof dependencies, no new nodes and no new Mathlib leaves.
- `citations.json`: 23 records, one literal statement excerpt for each citation in each proof step.
- `searches.jsonl`: actual msearch results for this item. The item's inherited Q20 searches remain intact; the additional Q06 searches are copied from this log with their actual outcomes.
- `report.md`: this report. `write_split.py` is sandbox-only generation scratch, not a delivered project file.

## Attachments

None. Searched `lean/WeilConjectures` for the exact blueprint tag, cofactor, and two-term determinant terminology. The only project cofactor hit concerns matrix independence, not this statement. No project declaration states the whole item. Its absence of a Lean audit record is not evidence of a finished proof.

## WANTED

None. All necessary sources are in the supplied literature or Mathlib source.

## Corrections and scope

The item had an empty proof. Its statement, statement dependencies, source, creation metadata and blueprint ancestry are retained. There is no statement dispute or weakened hypothesis. The source list already correctly describes this as an agent-formulated algebraic compatibility theorem; 0E9Y and 0FJM do not state it verbatim. I made `proof_origin.by = agent` and wrote the missing compatibility calculation explicitly.

The formula in duality.tex 0E9Y is useful even for a noninjective differential: the omitted basis/lift verification uses only alternation. I use that formula and prove well-definedness directly; I do not import an injectivity assumption from the source's wording of its sequence, nor its separate isomorphism-locus claim. The determinant comparison is exactly the kernel-first comparison required by the item. The target-first tensor ordering in the existing surjective calculus is converted to the item's dual-first ordering by ordinary tensor symmetry, without introducing a graded sign.

I read SETUP's three-level rule, the chapter and unit records, and GOAL.md. This item supplies determinant algebra below the lci fundamental-class prerequisite on the alteration/marked-curve branch of constructibility stability. It does not replace a unit step or change any chapter or target statement. The inherited `blueprint.from.node` is null; `blueprint_refs.py ancestor` also returns None. I retain that actual ancestry rather than inventing a blueprint node. `from.place` already names the precise alteration prerequisite and algebraic compatibility. Searches of the full imported blueprint for cofactor, two-term, projective complex, and determinant found no node stating this compatibility, so `same_as` remains empty.

## Unfinished work

None within the one-level stage-1 split. Existing dependencies retain their existing states; this delivery asserts no Lean proof or compiler validation. No Lean, repository, or launcher file was written, and no compiler or Lake command was run.

## Not duplicates

No new nodes were created. I searched the DAG by cofactor, good diagram, degreewise-surjective quasi-isomorphism, and the shared source tags 0E9Y/0FJM. I read the related determinant statements, including `lem-trf-two-term-perfect-determinant`, `lem-trf-affine-two-term-determinant`, and `lem-trf-surjective-two-term-determinant-calculus`. They give determinant comparisons and their calculus, not a map out of the rank-one cokernel or its compatibility with those comparisons. I cite the existing tools and keep the actual wedge calculation in this item's proof instead of creating a restatement of the item or a node for the contractible enlargement.

## Review by Q06

I read the displayed cofactor formula and omitted well-definedness check in `literature/stacks-project/duality.tex`, Tag 0E9Y, label lemma-determinant; the kernel-first exact-sequence comparison preceding and the good-diagram construction within `more-algebra.tex`, Tag 0FJM, label lemma-determinant-two-term-complexes; and the affine-local determinant and restriction statements in `perfect.tex`, Tags 0FJX/0FJY. I checked the labels against tags/tags. For local algebra I read algebra.tex 00NX (finite projective free covers), 00DM (exterior algebra and its free basis), 0C6F (localization), and 00EK (matching local module elements). I also read derived.tex 064B and the actual Mathlib declarations `CochainComplex.isKProjective_of_projective` and `CochainComplex.IsKProjective.Qh_map_bijective`. There are no new nodes needing further source checks.

For each step I opened every cited node's statement and checked the exact assertion used, not its proof:

1. The projective definition supplies splittings; the finite-projective cover theorem supplies finitely many unit-ideal generators and free localizations. The exterior basis theorem says that exterior powers of finite free modules are free on basis wedges. The exterior-localization node explicitly says the pure-wedge map is a module localization, and tensor-localization says the same for pure tensors. I wrote out why exterior powers preserve a split retract, and why the transpose of a finite idempotent identifies the localized dual. Thus no unstated general Hom-localization theorem or finite-presentation hypothesis is being used. Common refinements still generate the unit ideal.

2. The exterior definition supplies multilinearity and alternation, and the basis theorem supplies the rank-one top-wedge generator and degree-zero convention. The calculation expands a changed basis and a changed lift; the unit change-of-basis coefficient and its inverse cancel. A basis of Q is only a coordinate aid and is absent from the defining expression. This is an elementary verification, not a new lemma deferred elsewhere.

3. The cited cover exactness statement gives BOTH existence of a global module element from a matching family and injectivity of the localization map. I use its existence for each v, its uniqueness for linearity, and its injectivity to prove that u(P) is killed. Thus I glue values in the actual global module D(E); no uncited sheaf descent, localized-cokernel identification, or surjectivity of a map on global sheaf sections is needed.

4. The surjective determinant calculus expressly gives finite projectivity of the kernels, the isomorphism d_N, the kernel-first wedge maps, and the determinant trivialization. It applies because f is assumed degreewise surjective and a quasi-isomorphism between two-term finite projective complexes. The projective definition splits the quotient maps. The free-cover node applies also to the kernel. I choose l_i = d_N(k_i), so its determinant is 1 in these two bases. I treat zero charts separately and use rank c = r + c' only on nonzero charts.

5. The surjective calculus's displayed normalization gives the image of the kernel-first determinant generator. The exterior statements give the entire expansion: every correction lies in the span of the initial l_i, so every such wedge term repeats a basis vector. The final factor is the image of v, after all differential factors. This proves the coefficient equality rather than asserting it is transported. The cover theorem then detects the difference of the two maps on every global representative of a cokernel element. The exact determinant convention imposed in the statement identifies this T_f with D(f). No injectivity or maximal-minor nonvanishing is used.

6. The bounded-projective K-projectivity leaf applies with upper bound 0. The Hom-bijection leaf applies to this K-projective source and represents the given derived morphism by a homotopy class of actual chain maps. The derived-category definition explicitly gives its cohomology functors and the meaning of quasi-isomorphism, so the derived isomorphism makes that chain map a quasi-isomorphism. I am not inferring that an arbitrary derived morphism is a chain map without the K-projective input.

7. The projective definition and finite-free summand hypothesis give the surjection F onto P'. I wrote both components of t, the homotopy from fb, the kernel/cokernel computations for b, and the two surjectivity checks for t. The derived-category definition includes localization of the homotopy category, so homotopic chain maps have the same derived image. This is the explicit good diagram of 0FJM. The step creates no new comparison theorem and hides no existence of a common refinement. Direct summing with A^n changes the ranks by exactly n in both degrees.

8. The already proved surjective case applies to M as well as E and E'. The cited determinant theorem explicitly gives det(vu) = det(v)det(u); the derived definition gives cohomology functoriality and invertibility of H^0(b). The displayed equations then cancel H^0(b) on the right. This is all that remains of the general derived-isomorphism clause, rather than a second use of that clause as an assumption.

I checked delivery-errors B through E against these files. The citation file contains literal excerpts; the longer determinant and derived statements are retained whole in the quote where both their definitions and comparison clauses are used. Every proof citation belongs to proof_deps. Off-unit tools that are not Mathlib leaves are declared in split_report.tool_uses, for the maintainer to judge; none replaces a unit step. Every step is under 2000 characters. The finite-idempotent dual calculation, the basis expansion, and the explicit contractible enlargement are elementary arguments written in place; there is no separately assumed comparison or standard lemma hidden inside them.

For small cases, c = 0 gives w_E = id_Q under the degree-zero and degree-one exterior identifications. If u = 0 and c > 0, the wedge map is zero and the kernel-first calculation still holds. For a single added contractible summand and c' = 0 the wedge is d(k) followed by v, so the sign is +1, as the required normalization says. The same ordering works for arbitrary r and for r = 0. In characteristic two, all vanishings use x wedge x = 0, not division by 2. For the nonreduced example A = k[epsilon]/(epsilon^2), u:A to A^2, a maps to (epsilon a,0), the formula is w(x,y) = epsilon y: u is noninjective but the formula still kills its image, and no proof step cancels epsilon. For the zero ring every module and comparison is unique and all formulas hold. Finite projectives need not be globally free: every basis calculation is on the finite standard covers and equality is descended with 00EK.

Mathlib searches were run with the required msearch command in leanfinder, loogle, grep and leansearch, followed by a second leanfinder phrasing and a separate homological-algebra grep. I read all results. The actual cofactor hits `exteriorPower.cofactorLinear`, `exteriorPower.cofactorToLeft`, and `exteriorPower.cofactorToLeft_ιMulti_cons` in Algebra/Module/StablyFree/FreeOfInvertible.lean are summand-extraction maps with a chosen free complement; Matrix.cramer is a square-matrix map. Neither gives this determinant/cokernel compatibility. Semantic hits concerned homology maps, first exterior-power naturality and mapping cones, not the claimed comparison. No service failure was recorded as a negative mathematical result.
