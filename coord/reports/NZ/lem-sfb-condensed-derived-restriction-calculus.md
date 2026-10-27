# Stage-1 repair report

Item: lem-sfb-condensed-derived-restriction-calculus. Group: NZ. Date: 2026-10-22.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-derived-restriction-calculus.json: unchanged statement, five-step assembly, 1,751 proof characters.
- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-action-injective-infrastructure.json: statement-only, status unsplit, no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-restriction-mate-normalization.json: statement-only, status unsplit, no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-scalar-restriction-interchange.json: statement-only, status unsplit, no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-cup-mate-coherence.json: statement-only, status unsplit, no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-unipotent-boundary-naturality.json: statement-only, status unsplit, no exact Mathlib match.
- citations.json: verbatim excerpts of the five new cited statements; searches.jsonl: twenty genuine search calls.

## Attachments

None. Whole-library searches in lean/WeilConjectures for the blueprint id and derived/condensed invariants found discrete representation or generic derived declarations, not all clauses. The Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus declarations were also read; the relevant theorems contain sorry. They are not attachments.

## WANTED

WANTED: an exact external reference for the complete internal condensed action restriction, scalar, cup and connecting-class package of this item and its five new work packages. The blueprint paragraph (3) is the motivating application, not a source claiming these auxiliary results. Sources and proof origin are explicitly agent-formulated.
WANTED: the prior exact reference for the action-topos geometric restriction theorem remains as recorded in the retained Q04 report below.

## Findings and repair of the return

The return requested at least four independent statement-only nodes, comparable workloads, complete preservation of every old argument, and an assembly at most 3000 characters. This repair creates five nodes. The old twelve steps are assigned without omissions as follows. Their complete texts, citations and source places are retained verbatim below as handoff material for those nodes; they are not left as a long proof in the parent. Each new node has proof [], proof_deps [], proof_origin null and status unsplit, as required.

| New work package | Returned steps | Original argument characters |
|---|---|---|
| lem-sfb-condensed-action-injective-infrastructure | 1, 2, 3 | 2661 |
| lem-sfb-condensed-restriction-mate-normalization | 4, 5 | 2746 |
| lem-sfb-condensed-scalar-restriction-interchange | 6, 7 | 2288 |
| lem-sfb-condensed-cup-mate-coherence | 8, 9, 10 | 2569 |
| lem-sfb-condensed-unipotent-boundary-naturality | 11, 12 | 2039 |

The input sandbox was empty on this invocation. I copied the current read-only repository item, which contains the returned twelve-step argument and the maintainer corrections. I retained its complete statement, sources, mathlib_searches, blueprint/import metadata and review records. The prior Q04 report was read and is reproduced below. There was no prior sandbox searches.jsonl to reuse; fresh searches for each genuinely new statement were run through msearch.py, and their full outputs are recorded in the nodes. The parent old search records were preserved, not falsely represented as new calls. No statement dispute was found.

The statement keeps arbitrary topological groups, arbitrary internal commutative condensed rings, no flatness assumption, the actual normalized derived arrows, positive cocycle sign, and ordered products. The ancestor command reports null for the inherited created.item chain; the new from.node remains null and the via list prepends the parent, rather than inventing an imported ancestor. The chapter/unit and route are unchanged. This is not the unit key theorem, so its realization fields are untouched.

## Not duplicates

lem-sfb-condensed-action-injective-infrastructure vs lem-sfb-internal-action-site-presentation: The existing theorem is the underived action-site equivalence and creation of kernels/cokernels. The new work package constructs the invariant adjunction and derives it with canonical injective/shift normalizations; it also establishes the continuous-section sheaf input for arbitrary topological groups.

lem-sfb-condensed-action-injective-infrastructure vs lem-sfb-condensed-product-action-inflation: The existing statement is for profinite product groups, not arbitrary topological groups, and does not give the unbounded K-injective computation and canonical derived adjunction shifts.

lem-sfb-condensed-action-injective-infrastructure vs def-sfb-condensed-derived-invariants: The existing node specifies normalized data. The new statement asserts existence and computation, rather than treating a data specification as its proof.

lem-sfb-condensed-restriction-mate-normalization vs lem-trf-bounded-below-derived-mate-model: The existing statement is bounded below and generic. The new work package includes the unbounded internal-action mate, identifies its D+ restriction with those actual adjunctions and units, and retains the degree-zero, signed shift and last-arrow equations. The generic bounded-below theorem is a tool in the retained handoff, not another copy.

lem-sfb-condensed-restriction-mate-normalization vs lem-sp-canonical-right-derived-adjunction-shift: The existing statement controls shifts for an adjunction, not the identity of the concrete restriction mate with the normalized invariant-inclusion-derived arrow on action categories.

lem-sfb-condensed-scalar-restriction-interchange vs lem-sfb-ringed-comparison-tensor-adjunction: The existing theorem supplies a generic conjugate comparison for a ringed-topos isomorphism. The new statement constructs and normalizes the action-invariant scalar comparison and proves the actual coefficient/group exchange square for an arbitrary f, including its common transpose.

lem-sfb-condensed-scalar-restriction-interchange vs lem-sfb-open-scalar-conjugate-normalization: The existing comparison involves an open immersion and extension by zero on schemes. Here the objects are internal group actions and derived invariants and the conclusion is the restriction/coefficient interchange square.

lem-sfb-condensed-scalar-restriction-interchange vs def-sfb-condensed-derived-invariants: A definition of the scalar and group comparison data does not prove conjugacy, computation equations, shift compatibility or the exchange equality asserted here.

lem-sfb-condensed-cup-mate-coherence vs lem-sfb-monoidal-adjunction-mates: This generic theorem transfers (op)lax structures. The new statement also identifies the derived action tensorator, actual normalized group and scalar transformations, and their tensor/unit equations. Those concrete monoidality identifications are not a one-line instance of the generic existence theorem.

lem-sfb-condensed-cup-mate-coherence vs lem-sfb-monoidal-adjunction-unit-counit: The existing node gives monoidal units/counits of a specified monoidal adjunction. It does not identify the group and coefficient maps as monoidal for the actual action-site derived tensor comparisons.

lem-sfb-condensed-cup-mate-coherence vs lem-sfb-internal-inflation-graded-cup: That theorem treats profinite groups and identifies cup with graded composition under adjunction, with signs. It depends on this parent package. The new lemma constructs/coheres the cup pairings and their group/scalar maps, without invoking that downstream theorem.

lem-sfb-condensed-cup-mate-coherence vs lem-sfb-internal-bar-ordered-cup: The bar comparison realizes character cup products as bar cocycles and depends on the parent. This work package concerns derived tensor-of-counits coherence and does not assert any bar/cochain computation.

lem-sfb-condensed-unipotent-boundary-naturality vs def-sfb-condensed-unipotent-class: The existing definition pins the extension and positive class. The new theorem proves the restriction and coefficient maps preserve its canonical boundary, in the derived category with the stated shifts.

lem-sfb-condensed-unipotent-boundary-naturality vs lem-weil-pbc-complex-ses-triangle: The generic theorem supplies natural SES boundaries. The new statement constructs the concrete equivariant unipotent sequences, their actual maps and positive defect and identifies the images through the normalized derived functors.

lem-sfb-condensed-action-injective-infrastructure vs lem-sfb-condensed-derived-restriction-calculus: This work package covers only returned steps 1, 2, 3; it is one argument in the explicit human-requested re-split, not the whole theorem. The other four packages remain necessary.

lem-sfb-condensed-restriction-mate-normalization vs lem-sfb-condensed-derived-restriction-calculus: This work package covers only returned steps 4, 5; it is one argument in the explicit human-requested re-split, not the whole theorem. The other four packages remain necessary.

lem-sfb-condensed-scalar-restriction-interchange vs lem-sfb-condensed-derived-restriction-calculus: This work package covers only returned steps 6, 7; it is one argument in the explicit human-requested re-split, not the whole theorem. The other four packages remain necessary.

lem-sfb-condensed-cup-mate-coherence vs lem-sfb-condensed-derived-restriction-calculus: This work package covers only returned steps 8, 9, 10; it is one argument in the explicit human-requested re-split, not the whole theorem. The other four packages remain necessary.

lem-sfb-condensed-unipotent-boundary-naturality vs lem-sfb-condensed-derived-restriction-calculus: This work package covers only returned steps 11, 12; it is one argument in the explicit human-requested re-split, not the whole theorem. The other four packages remain necessary.

The sources of the new nodes are the actual agent-formulated blueprint/application place, not invented Stacks tags. The supporting Stacks facts are preserved below under their exact tags and labels. Whole-DAG keyword searches and blueprint_refs.py searches were run before node creation; nearby definitions, generic tools and the profinite/downstream results listed above were read. No equivalent blueprint statement was found.

## Review by NZ

I read delivery-errors B–E in full (including the retained second copy), the chapter/unit, the item and all twelve old steps, the defining condensed action/invariant/tensor/class records, the existing related statements listed in Not duplicates, and the main-20261015 direct-images proof paragraph (3). The latter is about proper/open direct images: it does not prove this auxiliary calculus, so I retained the agent-origin attribution and exact-reference WANTED rather than claiming an external theorem. The Q04 report below supplies the historical corrections, and I read the current canonical mate-model, bounded-below derived-adjunction and right-derived-plus statements to keep the maintainer’s D+ bridge intact.

For sources of new node 1 I read Stacks sites-modules.tex lemma-abelian (03DA), lemma-limits-colimits (03DB), derived.tex lemma-enough-injectives-right-derived (05TI), lemma-enough-K-injectives-implies (070K), lemma-derived-adjoint-functors (09T5), and injectives.tex theorem-K-injective-embedding-grothendieck (079P), together with the existing action-site theorem. For node 2 I read the same derived-adjunction input and derived.tex lemma-adjoint-is-exact (0A8D), and the actual canonical shift and bounded-below mate-model node statements; these are the sources of the normalization argument, not a claim that 0A8D alone identifies the fixed shift. For node 3 I read sites-cohomology.tex lemma-derived-pullback-composition (0D6D), lemma-adjoints-push-pull-compatibility (0FPI) and the ringed-composition/monoidal-comparison statements. For node 4 I read sites-cohomology.tex lemma-symmetric-monoidal-derived (0FPT), lemma-pullback-tensor-product (07A4), lemma-adjoint (07A6), and the monoidal mate/unit-counit statements. Stacks explicitly omits some coherence details: the existing monoidal comparison nodes carry them, and the old explicit transposes are preserved below. For node 5 I read the action-site exactness statement and the canonical SES-triangle and exact-functor-image statements, which state the actual connecting-square equations used. Its explicit triangular action and positive defect remain agent-written, not attributed to a nonexistent source theorem.

Assembly step 1 cites only the first new statement, which explicitly supplies sheafhood, created exactness, Grothendieck structure, the invariant-submodule Hom adjunction, exact scalar/group/trivial restrictions, K-injective and bounded-below injective computations and the canonical adjunction shifts. Smallness and section sizes are stated in every package; J is not assumed profinite. The closed-quotient continuity argument of old step 1 is retained in the first handoff. Thus none of these facts is taken just from a definition.

Assembly step 2 uses exactly the second new statement’s mate and computation-unit equations, its D+ identification (with counit normalization), degree-zero identification, shift/last-arrow compatibility and identity case. It does not apply a bounded-below theorem directly to an arbitrary unbounded object. The old D+ bridge is retained verbatim in its handoff. The sentence and formulas quoted in citations.json occur literally in the new statement.

Assembly step 3 uses the third statement’s actual scalar conjugate and common-transpose equation. Its hypotheses allow arbitrary phi and arbitrary derived f; no assertion that scalar restriction preserves injectives or that scalar extension is underived is used. Source and target of the Hom bijection and both paths were checked: each transpose is U(f) after U(epsilon_J). The coefficient equality is already a derived-arrow equality, not a per-degree replacement.

Assembly step 4 uses the fourth statement’s actual tensor-of-counits pairing and its unit, associativity and two concrete monoidality results. Its equations are for the canonical K-flat-derived tensors, not unlocalized section tensors. The group equation includes F_H(t_U inverse), which fixes its source/target; the coefficient target uses the lax scalar pairing. The full argument showing monoidality of the scalar conjugate through units, left comparison and counits remains in the handoff. Ordered products include length zero and do not permute factors.

Assembly step 5 uses the fifth statement’s constructed sequence, positive defect and two actual maps of extensions, together with the products established in step 4. The scalar class formula retains the domain map phi[-1] and its canonical scalar shift comparison. The middle map (phi,phi) is equivariant by multiplicativity, and the endpoint map takes 1 to 1. Every non-elementary input of the assembly is the conclusion of a cited node, and citations.json quotes literal substrings; there are no new proof steps concealed inside a statement-only node.

I checked trivial J and H, identity u and phi, the zero ring, the empty profinite test object, zero character (equivariant splitting), a noncommutative J (characters still land additively), characteristic two (the defect remains +a), the nonflat map Z to Z/2, and ordered products of zero and one factor. These tests introduce no additional hypotheses. Generalized fixed sections, rather than fixed global points only, are retained throughout. None of the new statements asserts continuous-cochain acyclicity. All comparison/isomorphism statements live in the ordinary derived category; their degree-zero consequences are explicitly identified.

The five handoff arguments contain respectively 2661, 2746, 2288, 2569, 2039 characters, so the work was distributed comparably. The assembly has no long proof step. The new nodes have no proof/proof_deps; downstream generic tools are not duplicated and the parent is not cited by any new statement. I wrote only this sandbox and ran no Lean/compiler/Lake/build, no local DAG/preflight checker, no repository git command and no launcher modifications. There was no pre-existing sandbox report or search log to overwrite.

## Remaining work

No unresolved mathematical obstruction to this one-level repair. The five statement-only nodes deliberately await their own workers. The required server dry run and delivery are recorded at the end after execution.

## Complete handoff of the returned arguments

These are the complete returned proof texts assigned to the new nodes, not new node proof fields. They are retained verbatim so future workers receive every argument and every old dependency, including the independent reviewer’s D+ normalization correction. Each new statement above specifies the conclusion its assigned argument must establish.

### lem-sfb-condensed-action-injective-infrastructure

Returned step 1:

Work in one coefficient universe containing the small profinite site and the section sets $C(S,J)$ for the groups used. The presheaf $\underline J$ is a group sheaf: maps into $J$ descend along finite jointly surjective maps of profinite spaces because their finite disjoint union is a surjection between compact Hausdorff spaces. It is closed (compact subsets have compact, hence closed, images), hence is a quotient map; therefore the descended functions are continuous. Convert internal modules to sectionwise ring-sheaf modules. Apply the action-site presentation with $K=\underline J$. It identifies $\mathcal A_R(J)$ with module sheaves on the small ringed site $C_K$, creates kernels and sheafified cokernels on the underlying site, and detects zero objects. Consequently it creates exactness. The small ringed-site Grothendieck theorem applies to $R_K$, and also to the base ring sheaf $R$; no profiniteness of $J$ is required here.

Uses: def-weil-pbc-internal-abelian-sheaf-module-equivalence, lem-sfb-internal-action-site-presentation, lem-pur-ringed-site-grothendieck-abelian.

Source: literature/stacks-project/sites-cohomology.tex — Tag 07A5, section-unbounded; Modules on Sites Tags 03DA and 03DB; action-site specialization.

Returned step 2:

Write $T_J$ for trivial inflation. Define $\Gamma_JM(S)$ to consist of the sections fixed after every $V\to S$. This is an $R(S)$-submodule stable under restriction. It is a sheaf: glued sections remain fixed since the equality $g\cdot m|_V=m|_V$ can be checked on the base changes of a covering of $S$. An equivariant $h:T_JA\to M$ lands in this subsheaf, since $g h(a|_V)=h(a|_V)$; conversely composition with its inclusion is equivariant. These two operations are inverse and natural, proving the specified adjunction and its normalization. Trivial inflation and group restriction leave the underlying modules and maps unchanged, hence are additive and exact by step 1. Scalar restriction does the same to underlying abelian sheaves and their kernels and sheafified cokernels, hence is also exact. This constructs the datum of [def-sfb-condensed-action-module], rather than assuming its existence.

Uses: def-sfb-condensed-action-module, lem-sfb-internal-action-site-presentation.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), agent expansion of the internal derived-restriction input.

Returned step 3:

Apply the bounded-below injective-resolution theorem on $C_K$ and the Grothendieck K-injective existence theorem. Thus equivariant injective resolutions compute $F_J:=R\Gamma_J$ on bounded-below objects, and K-injective resolutions compute it on all ordinary derived objects. Termwise invariants preserve sums of maps and homotopies, so their descent on K-injective representatives is additive; the right-derived-functor theorem makes $F_J$ triangulated. Exact $T_J,u^*,s$ descend termwise with the canonical signed shifts. The canonical derived adjunction is $D(T_J)\dashv F_J$; denote its unit and counit by $\eta_J,\varepsilon_J$. It is the adjunction of the original fixed-section Hom bijections, not a newly chosen adjunction on isomorphic functors. Its unit and counit commute with the canonical K-injective shifts.

Uses: lem-sc-bounded-below-injective-resolution, lem-sfb-grothendieck-k-injective, def-sfb-right-derived-functor, lem-pc-right-derived-functor-triangulated, lem-weil-pbc-exact-functor-derived-factorization, lem-pc-derived-adjoint-functors, lem-sp-canonical-right-derived-adjunction-shift.

Source: literature/stacks-project/derived.tex — Tags 05TI, 070K, 09T5, 0A8D; injectives.tex Tag 079P.


### lem-sfb-condensed-restriction-mate-normalization

Returned step 4:

For $u:H\to J$ use the geometric restriction $q_u$ and projections $p_J,p_H$ of [lem-sfb-action-topos-geometric-restriction]. In the derived categories put $U=D(u^*)$, $L_J=D(T_J)$ and $L_H=D(T_H)$, so $UL_J=L_H$ with the specified localization comparisons. Define
$$b_{u,N}=F_H(U\varepsilon_{J,N})\circ\eta_{H,F_JN}:F_JN\longrightarrow F_HUN.$$
Its transpose under $L_H\dashv F_H$ is $U\varepsilon_{J,N}$. It is natural by naturality of the unit and counit. In the underived adjunction the very same transpose is the inclusion $\Gamma_JN\hookrightarrow\Gamma_Hu^*N$. On $D^+$: bounded-below injective resolutions are K-injective [lem-sc-bounded-below-injective-resolution], so $F_J,F_H$ preserve $D^+$ and, with their units (invertible on these resolutions), restrict to bounded-below right derived functors, identified with $\mathbf R\Gamma_J,\mathbf R\Gamma_H$ compatibly with the comparison units $\alpha$ by clause (3) of [lem-weil-pbc-right-derived-plus-injective]. At a bounded-below injective $P$ the counit of $L_J\dashv F_J$ is the class of the termwise counit $T_J\Gamma_JP\to P$ (step 3), which is the counit identity of [lem-trf-bounded-below-derived-adjunction]; as $\alpha_P$ is invertible and every object of $D^+$ is such a $QP$, the restricted adjunctions are the canonical bounded-below ones. Apply [lem-trf-bounded-below-derived-mate-model] with $L=T_J$, $R=\Gamma_J$, $L'=T_H$, $R'=\Gamma_H$, $G=\mathrm{id}$, $H=u^*$ and $\sigma$ the identity $T_H=u^*T_J$; its underived mate is the inclusion. The canonical bounded-below derived-mate comparison says precisely that the displayed mate is induced by that inclusion and the two derived-functor units; equivalently, resolving $N\to I$ and $u^*N\to J'$, it is $\Gamma_JI\to\Gamma_Hu^*I\to\Gamma_HJ'$. On arbitrary complexes the mate formula gives the total derived restriction with this normalization, using the canonical derived adjunctions.

Uses: lem-sfb-action-topos-geometric-restriction, lem-trf-bounded-below-derived-mate-model, lem-pc-derived-adjoint-functors, lem-sc-bounded-below-injective-resolution, lem-weil-pbc-right-derived-plus-injective, lem-trf-bounded-below-derived-adjunction.

Source: literature/stacks-project/derived.tex — Tag 09T5 and the canonical derived-mate construction; bounded-below normalization from lem-trf-bounded-below-derived-mate-model.

Returned step 5:

The expression for $b_u$ is a composite of whiskered units and counits of exact-left derived adjunctions. They commute with the fixed integer shifts by [lem-sp-canonical-right-derived-adjunction-shift], and this property survives composition and whiskering. Given a triangle $A\to B\to C\xrightarrow{\delta}A[1]$, naturality at all four arrows, followed by the shift equation at the last one, gives a morphism of the two image triangles; in particular $b_{A}[1]F_J(\delta)=F_HU(\delta)b_C$ after the canonical shift identifications. For a module $M$, left exactness gives $H^0(\Gamma_JI)=\Gamma_JM$ from $0\to M\to I^0\to I^1$, so the resolution formula in step 4 is the invariant inclusion in degree zero. For $u=\mathrm{id}$ and trivial groups, its transpose is the identity-adjunction counit, and the triangle identity gives $b_u=1$.

Uses: lem-sp-canonical-right-derived-adjunction-shift, lem-weil-pbc-commshift-nattrans-comp-whisker, lem-weil-pbc-mate-pasting.

Source: literature/stacks-project/derived.tex — Tag 0A8D (canonical adjoint shift); elementary last-arrow and degree-zero checks.


### lem-sfb-condensed-scalar-restriction-interchange

Returned step 6:

For $\varphi:R\to R'$ write $s_0$ for scalar restriction on base modules, $s_J$ for scalar restriction on $J$-actions, and $E_0,E_J$ for their derived left adjoints (derived scalar extension). These are ringed-topos operations on the identity underlying topoi. The commuting square of ringed morphisms in [lem-sfb-action-topos-geometric-restriction] gives the canonical monoidal comparison
$$E_JL_J^R\cong L_J^{R'}E_0.$$
Take its conjugate under the composite derived adjunctions to obtain
$$d_J:F_J^R s_J\xrightarrow{\sim}s_0F_J^{R'}.$$
The ringed derived-composition theorem supplies this conjugate and its computation-unit normalization even though $s_J$ need not preserve injectives. In degree zero its two underived right adjoints agree as the same fixed-section submodule: $\Gamma_{R,J}s_J=s_0\Gamma_{R',J}$. For $f:N\to s_JN'$ define $c_J=d_{J,N'}\circ F_J^R(f)$. This construction uses derived extension of scalars, so places no flatness assumption on $\varphi$. The scalar pullback-composition comparison is degreewise on flat-term K-flat representatives and hence commutes with their signed shifts. The scalar derived adjunctions have shift-compatible units and counits by [lem-weil-pbc-derived-adjunction-shift]. Expressing $d_J$ by these units, comparison and counits therefore also makes it shift compatible, and thus a morphism on image triangles.

Uses: lem-sfb-action-topos-geometric-restriction, lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-weil-pbc-derived-adjunction-shift.

Source: literature/stacks-project/sites-cohomology.tex — Tags 0D6D, 0D6E, 07A6 and 0FPI, applied to the identity coefficient morphisms and p_J.

Returned step 7:

Here is the coefficient/restriction equality, retaining its actual arrows. For every $X\in D(R)$ the scalar and trivial-inflation adjunctions identify
$$\operatorname{Hom}(X,s_0F_H^{R'}U'N')=\operatorname{Hom}(L_H^RX,s_HU'N'),$$
where the right-hand category is that of derived $R$-linear $H$-actions and $U'=D(u^*)$ for $R'$-actions. This identification uses $E_HL_H^R=L_H^{R'}E_0$ and $E_H\dashv s_H$. Take $X=F_J^RN$. Transpose each of the two proposed composites using this bijection. The defining counit equation for $d_H$ or $d_J$, followed by that for $b_u$, turns both into the same morphism
$$L_H^RF_J^RN=UL_J^RF_J^RN\xrightarrow{U\varepsilon^R_{J,N}}UN\xrightarrow{U(f)}Us_JN'=s_HU'N'.$$
This is also the mate-pasting identity for the commuting scalar and group squares. Injectivity of the Hom bijection proves $c_Hb_u(N)=s_0(b_u(N'))c_J$. The argument takes place in the derived category, prior to taking cohomology.

Uses: lem-weil-pbc-mate-pasting, lem-sfb-ringed-derived-monoidal-comparisons.

Source: literature/stacks-project/sites-cohomology.tex — Tags 0E46, 0E47 and 0FPI; the written transposition verifies the particular square.


### lem-sfb-condensed-cup-mate-coherence

Returned step 8:

The base module category and the action-site module category have the ordinary K-flat derived symmetric monoidal structures of [lem-sf-ringed-derived-closed-symmetric-monoidal]. By [lem-sfb-ringed-derived-monoidal-comparisons], $L_J$ is strong monoidal, with the actual diagonal-action tensor comparison, and all scalar and group pullback comparisons above are monoidal. Transfer the inverse tensor comparison across $L_J\dashv F_J$. This gives the lax pairing $\mu_J:F_JA\otimes_R^{\mathbf L}F_JB\to F_J(A\otimes_R^{\mathbf L}B)$ and unit $e_J:R[0]\to F_JR[0]$. Its transpose is the tensor of counits
$$L_J(F_JA\otimes^{\mathbf L}F_JB)\cong L_JF_JA\otimes^{\mathbf L}L_JF_JB\xrightarrow{\varepsilon_{J,A}\otimes\varepsilon_{J,B}}A\otimes^{\mathbf L}B.$$
The mate theorem gives the associativity and both unit identities, and the monoidal-unit/counit theorem gives their compatibility with the actual adjunction. Apply $F_J$ to the regular-ring multiplication and compose with $\mu_J$: this is the asserted unital derived cup product on $C_R(J)$.

Uses: lem-sf-ringed-derived-closed-symmetric-monoidal, lem-sfb-ringed-derived-monoidal-comparisons, lem-sfb-monoidal-adjunction-mates, lem-sfb-monoidal-adjunction-unit-counit.

Source: literature/stacks-project/sites-cohomology.tex — Tags 0FPT, 07A4 and 07A6; lax structure obtained by the explicit tensor-of-counits transpose.

Returned step 9:

Group restriction preserves this pairing. Indeed transpose the two maps from $F_JA\otimes^{\mathbf L}F_JB$ to $F_HU(A\otimes^{\mathbf L}B)$ under $L_H\dashv F_H$. The path through $b_{u,A\otimes B}\mu_J$ and the path through $\mu_H(b_{u,A}\otimes b_{u,B})$ both become $U(\varepsilon_{J,A}\otimes\varepsilon_{J,B})$, using $UL_J=L_H$ and the monoidal comparison for $U$. The unit equation follows by the same transpose with the regular ring. This proves the binary-product and unit equations for $b_u$ on $C_R(J)$, with the specified multiplication, rather than only equality on cohomology.

Uses: lem-sfb-ringed-derived-monoidal-comparisons, lem-sfb-monoidal-adjunction-unit-counit.

Source: literature/stacks-project/sites-cohomology.tex — Tag 07A4 and the tensor-of-counits transpose of step 8.

Returned step 10:

For coefficient change use the strong monoidal scalar extensions $E_0,E_J$ and their lax right adjoints $s_0,s_J$. The comparison $E_JL_J^R\cong L_J^{R'}E_0$ is monoidal, and its conjugate $d_J$ is compatible with the lax pairings: expand its definition as a unit, the inverse monoidal left comparison, and a counit. Units and counits are monoidal by [lem-sfb-monoidal-adjunction-unit-counit]; composing their tensor and unit equations therefore gives those for $d_J$. The regular-ring map $R[0]\to s_JR'[0]$ is an algebra map, since on pure tensors $\varphi(xy)=\varphi(x)\varphi(y)$ and $\varphi(1)=1$. Thus $c_J=d_JF_J(\varphi)$ is an algebra map to $s_0C_{R'}(J)$, equipped with the lax scalar-restriction product. Binary product compatibility gives compatibility with every ordered finite cup product by induction on its length; length zero is the unit case. Nothing permutes the factors, so the usual graded signs are retained.

Uses: lem-sfb-ringed-derived-monoidal-comparisons, lem-sfb-monoidal-adjunction-mates, lem-sfb-monoidal-adjunction-unit-counit.

Source: literature/stacks-project/sites-cohomology.tex — Tags 07A4, 0D6D and 0FPI; monoidal conjugate expanded through its unit and counit.


### lem-sfb-condensed-unipotent-boundary-naturality

Returned step 11:

For an additive sheaf-group map $a:\underline J\to(R,+)$ define $E_a=R\oplus R$ with $j(x,y)=(x+a(j)y,y)$. The action equation follows from $a(jk)=a(j)+a(k)$; the inverse uses $-a(j)$. The maps $i(x)=(x,0)$ and $p(x,y)=y$ are equivariant with trivial action at the endpoints. Their underlying split exact sequence is therefore exact in the action category by step 1. Use the canonical short-exact-sequence triangle of [lem-weil-pbc-complex-ses-triangle]. Let $\partial_a:R[0]\to R[1]$ be its derived connecting arrow. Define
$$[a]=\bigl(F_J(\partial_a)\circ e_J\bigr)[-1]:R[-1]\to C_R(J),$$
using the canonical shift comparison. This is exactly the connecting class evaluated at $1$. For its inhomogeneous degree-one representative take the underlying splitting $t(y)=(0,y)$. Its equivariance defect is $jt(1)-t(1)=(a(j),0)$, giving the prescribed positive cocycle $a$. This computes the extension's cocycle; it makes no assertion that underived continuous cochains compute the derived functor.

Uses: lem-sfb-internal-action-site-presentation, lem-pc-right-derived-functor-triangulated, lem-weil-pbc-complex-ses-triangle.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), agent-formulated degree-one restriction input; explicit split-extension construction.

Returned step 12:

Restriction sends this exact sequence literally to $E_{a\circ u}$, with the same inclusion, projection and splitting. Exact functor/short-exact-sequence triangle compatibility identifies its boundary with the restricted boundary. Apply the morphism of derived triangles from step 5: its connecting square and the unit equation give $b_u[a]=[a\circ u]$. For scalar change the map of exact sequences has endpoint maps $\varphi$ and middle map $(x,y)\mapsto(\varphi(x),\varphi(y))$. Equivariance holds because $\varphi(x+a(j)y)=\varphi(x)+\varphi(a(j))\varphi(y)$; its target is $s_JE_{\varphi\circ a}$. Apply the triangulated functors and the canonical scalar comparison of step 6 to this diagram. The connecting square gives $c_J[a]=[\varphi\circ a]$, since its quotient map takes $1$ to $1$. Together with steps 9 and 10 this proves the asserted identities for all ordered products of the classes, including the empty product. For $a=0$ the splitting is equivariant and the class is zero; trivial groups and the zero ring give the same formulas.

Uses: lem-pc-right-derived-functor-triangulated, lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-pbc-complex-ses-triangle, lem-weil-pbc-exact-functor-ses-triangle-image.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Paragraph (3), explicit restriction and scalar maps of the unipotent extensions, with their connecting squares.


## Retained prior stage-1 report (Q04)

# Stage-1 worker report

Item: lem-sfb-condensed-derived-restriction-calculus. Group: Q04. Date: 2026-10-22.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-derived-restriction-calculus.json: statement, split into twelve proof steps; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-action-topos-geometric-restriction.json: one new statement-only foundation node, unsplit; no Mathlib match. It supplies geometric morphisms for restriction of internal sheaf-group actions and their coefficient squares, before any derived invariants or cup products.
- citations.json: one verbatim statement excerpt for every node cited in every proof step, numbered from 1.
- searches.jsonl: actual msearch results, retained. The node search records use the logged tool names and exact queries. Local helper scripts only construct/review the JSON; no Lean or compiler was run.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for condensed actions, invariants, classifying topoi and sheaf-group coinduction. No project declaration gives all clauses. The ordinary representation cohomology declarations do not have internal condensed-ring coefficients. The existing CondensedActionModule and CondensedProductActionInflation files under Sheaf are not whole-item attachments; the latter also treats profinite groups only.

## WANTED

WANTED: an exact non-SGA reference for the classifying topos of a group object in a Grothendieck sheaf topos and the geometric restriction maps, for lem-sfb-action-topos-geometric-restriction. Stacks Tag 00W0, sites.tex proposition-sheaves-on-group, was read but states only the ordinary-group case. It is recorded as context, not claimed as the general theorem.

WANTED: an exact external reference stating the entire internal condensed-ring restriction/cup/scalar package of the item. The blueprint paragraph (3) and Bhatt–Scholze section 4.3 do not state this package. The delivered proof is explicitly agent-written, using the individual cited categorical theorems instead of attributing the whole package to either source.

## Findings and corrections

The item statement is unchanged, including arbitrary topological groups, arbitrary commutative condensed rings, the absence of a flatness hypothesis, the positive degree-one normalization, and ordered derived cup products. No statement dispute was found. The small-site/section-set universe convention is applied explicitly.

The previously unsplit item gave no argument. The proof now constructs the invariant adjunction and the unipotent extension explicitly, defines the restriction transformation by its counit transpose, and checks the coefficient square by transposing its two composites to the same map. Scalar restriction is exact but need not preserve injectives; it is never applied as though it did. Instead its derived comparison is the conjugate of the scalar/trivial-inflation pullback square, using the ringed-topos derived-composition theorem. The scalar comparison is an isomorphism for this square, although the item only needs the resulting map.

The nearest blueprint ancestor reported by tools/blueprint_refs.py ancestor is null, inherited from the item's created.item chain. I retained that result and filled the precise paragraph (3) place and via chain, rather than inventing an ancestor id. The unit is not this item's key theorem, so no realization fields were changed.

## Not duplicates

lem-sfb-action-topos-geometric-restriction vs lem-sfb-internal-action-site-presentation: the existing statement presents equivariant module sheaves on one action site and creates kernels/cokernels. It does not construct the topos of set-valued actions, prove restriction has a right adjoint as a left exact functor on that topos, or identify the geometric coefficient squares. The new node states precisely that geometric structure. It asserts no derived restriction transformation, connecting class, coefficient comparison or cup-product theorem.

lem-sfb-action-topos-geometric-restriction vs lem-sfb-condensed-product-action-inflation: the existing theorem treats invariants and inflation for products of profinite groups. The new node treats geometric restriction for arbitrary morphisms of group sheaves on an arbitrary small base site and does not state the existing theorem's invariant/product adjunction calculation.

lem-sfb-action-topos-geometric-restriction vs lem-sfb-condensed-derived-invariant-bar: the bar node is a derived model for a profinite group's invariants using derived internal Hom. The new node is underived geometric infrastructure, with neither a bar model nor a cochain acyclicity assertion.

lem-sfb-action-topos-geometric-restriction vs lem-sfb-constant-scalar-geometric-adjunctions: the latter assumes a geometric morphism and compares constant-ring/fixed-ring encodings. The new node constructs the action restriction geometric morphism, and its coefficient rings are arbitrary sheaves rather than constant sheaves.

No existing DAG node cites the context tag 00W0. Blueprint searches for classifying and equivariant, and whole-DAG searches for action-site, coinduction and geometric restriction, found no node with the new statement. Generic monoidal adjunctions, ringed-site derived tensor, right derived functors and shift lemmas were reused rather than recreated. Recorded Mathlib hits for ordinary Rep.resCoindAdjunction, generic sheaf pullback adjunctions, and rightDerived shift machinery were read as differently typed inputs, not claimed to formalize internal sheaf-group restriction in one line.

## Review by Q04

I read the current item, its defining action node, the chapter and unit records, and main-20261015's direct-images proof paragraph (3). That paragraph concerns proper/open direct images and does not itself establish the auxiliary restriction calculus. This explains the agent proof origin and the WANTED entries. I also read the new node against the existing action-site statement and Stacks sites.tex proposition-sheaves-on-group (00W0), rather than treating an ordinary abstract group as a sheaf of groups.

For the new node the underlying intended argument is the set-valued analogue of the explicit twisted-arrow presentation. For a morphism theta:L→K, the right adjoint to restriction is internal coinduction: the subobject of the exponential X^K cut out by f(theta(l)k)=l f(k), with (g·f)(k)=f(kg). Evaluation at 1 and the map m↦(k↦h(km)) are inverse adjuncts. Restriction creates finite limits. Trivial action has the all-generalized-sections invariant right adjoint. These give the claimed geometric morphisms, and the identity on underlying sheaves identifies their coefficient squares. This argument is recorded here, not hidden as a proof sketch inside the statement-only new node. Small-site presentation and internal exponent existence remain part of splitting that new foundation node later. It is a genuine structural input, not a clause of the derived item renamed.

I checked the proof steps individually against their cited statements:

1. The internal-module equivalence preserves underlying sections; the existing action-site theorem explicitly gives the small ringed-site presentation, kernel and sheafified-cokernel creation, and zero detection. The Grothendieck node applies to any small ringed site, not only schemes. C(S,J) is a sheaf for arbitrary J: the finite covering map is a compact-Hausdorff closed surjection, hence quotient. No profiniteness hypothesis on J has been silently used.
2. The action definition specifies, but does not assert existence of, normalized invariants. The step constructs the subsheaf, verifies its sheaf condition after base change of covers, and proves both transpose formulas. The only structural exactness input is the action-site kernel/cokernel statement from step 1. Changing the scalar action does not change the underlying sheafified cokernel.
3. The bounded-below resolution theorem is for arbitrary small ringed sites, which include the action presentation. The Grothendieck K-injective theorem is unbounded. The definition of total right derived functor specifies its resolution normalization; the triangulated-functor theorem gives the fixed shift/triangle behavior. Exact descent supplies termwise functors. The canonical derived-adjoint theorem and canonical-right-derived-adjunction-shift node apply because trivial inflation is exact and additive and has the constructed right adjoint. These are cited for their statements, not their proofs.
4. The new node supplies the actual geometric restriction and equality U L_J=L_H. The b formula is the adjunction mate of that equality, with transpose U epsilon_J. The existing bounded-below mate-model node permits an arbitrary exact H and explicitly does not assume preservation of injectives; it gives the comparison-unit equation and therefore identifies this mate with the invariant inclusion on modules and bounded-below resolutions. On the full derived categories the displayed mate defines the canonical total restriction.
5. The canonical shift theorem controls the chosen K-injective shifts. The composition/whiskering node states the exact closure properties used. Naturality at the triangle's last arrow together with the shift identity gives the connecting square, which is written out. Left exactness computes H^0 from the start of an injective resolution. Identity mates are explicitly covered by the mate-pasting node's identity clause.
6. The new node supplies commuting ringed coefficient squares. The ringed derived-monoidal comparison theorem applies to arbitrary commutative ring sheaves and explicitly has no flatness assumption. Its composition and adjunction normalization, together with the derived-pushforward-composition statement, give d_J as the conjugate of E_J L_J=L'_J E_0. The scalar derived-adjunction-shift node applies even when underived scalar extension is not exact; the K-flat comparison is degreewise and commutes with signed shifts. I added this check so the later scalar connecting square uses the recorded shifts.
7. The two coefficient/restriction paths are compared inside a specified Hom bijection. Their common transpose is the displayed U(f) after U epsilon_J. The mate-pasting node states exactly the composition principle, and the ringed comparison node supplies canonical adjunction normalization for the scalar comparisons. This proves equality of derived morphisms, not merely of their induced cohomology maps.
8. The ringed derived symmetric monoidal theorem applies on both base and action sites. The ringed derived comparison theorem gives strong monoidality of L_J with its actual comparisons. The monoidal mate theorem produces the lax right adjoint; the monoidal unit/counit theorem gives coherence for the same adjunction. The tensor-of-counits formula is displayed and specializes to multiplication on the regular ring.
9. This is the elementary double-transpose calculation from step 8, not a new monoidality lemma: both composites transpose to U(epsilon_A tensor epsilon_B). The monoidal comparison and monoidal unit/counit statements are precisely the inputs needed to identify this transpose, including the unit.
10. The scalar comparison is the conjugate of a monoidal left comparison. Its expression through units/counits, whose monoidality is the cited statement, proves its tensor and unit equations. The regular-ring map is multiplicative even for a nonflat ring map, and induction preserves the given ordering of factors. Nothing here identifies derived tensor with underived tensor on arbitrary coefficients.
11. I checked the group law and inverse of the unipotent action, equivariance of inclusion/projection, and exactness by the existing creation theorem. The canonical triangle is supplied explicitly by lem-weil-pbc-complex-ses-triangle (Stacks 0152); the map [a] is its shifted derived boundary evaluated on the unit. The defect j(0,1)-(0,1)=(a(j),0) fixes the positive sign. It is an extension cocycle calculation and uses no continuous-cochain acyclicity theorem.
12. Restriction sends the extension itself to E_(a∘u). Scalar change uses the explicitly written map (phi,phi), which is equivariant by the written multiplication identity. The generic complex-SES triangle node gives naturality for the displayed sequence map, and lem-weil-pbc-exact-functor-ses-triangle-image identifies the canonical triangle after restriction (Stacks 0151/0152). The triangle/shift comparisons established earlier then give the two connecting squares, and phi(1)=1 identifies the evaluated quotient section. This checks the actual normalized classes and, with the algebra-map steps, their ordered products.

I tested trivial groups (the induced restriction is the identity), the zero ring, a zero additive character (the extension splits equivariantly), noncommutative groups (a is an additive homomorphism), the empty profinite test object, identity coefficient maps, a nonflat coefficient map Z→Z/2, and the cup product of zero or one factor. The nonflat test is exactly why I avoided a claim that scalar restriction preserves injectives. Characteristic 2 does not change the defect formula; products retain the ambient Koszul conventions. No strengthened group/ring hypothesis or weakened conclusion was introduced.

I checked delivery-errors B–E: the new statement introduces all of its objects, has no proof/proof_deps, and has actual logged searches with two semantic phrasings; existing more general nodes were reused. Every step's cited statement is open and quoted verbatim in citations.json. Non-elementary facts have nodes, while the invariant adjunction construction, two transposition checks and unipotent-sequence computations remain explicit steps. All steps are below 2000 characters. No cycle or SGA route is introduced. Only this sandbox was written, and no Lean, Lake, compiler, local DAG checker, repository git command or launcher edit was run.

## Remaining work

No part of this one-level split is left unfinished. The new unsplit foundation lemma deliberately remains for a later stage-1 item. Its exact external reference is WANTED as above. Server check_dag and review_split passed before the final scalar-shift refinement; the first full dry run passed at 8d77e83775f. A final citation audit added the existing short-exact-sequence triangle/naturality and exact-functor-compatibility nodes to steps 11–12, without changing the argument; the final dry run and push follow that correction.

