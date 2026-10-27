# Worker report: lem-sfb-relative-flat-locus-base-change

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-flat-locus-base-change.json: repaired split; statement and statement dependencies unchanged; three-step assembly of 1048 characters.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-flat-affine-charts.json: statement, unsplit, no Mathlib match; old steps 1–2.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-flat-fibre-test.json: statement, unsplit, no Mathlib match; old steps 3–4.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-residue-fibre-square.json: statement, unsplit, no Mathlib match; old steps 5–6 (the application of pointwise ascent/reflection remains in the parent).
- report.md and citations.json; searches.jsonl contains the actual msearch log. repair.py is a sandbox-only editing helper.

## Attachments

No attachment for the item: lean/Sheaf/AlgebraicGeometry/RelativeFlatLocusBaseChange.lean:82–95 states it with a sorry. Searches under lean/WeilConjectures for its blueprint tag and flat-locus terminology found no exact finished declaration.
AlgebraicGeometry.locallyOfFinitePresentation_of_comp belongs to lem-a1-map-over-base-finite-presentation (WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean:53). This is already attached live and is reused as the available cancellation input in the affine-chart handoff; no duplicate node or edit to it.

## Literature wanted

WANTED: none. All mathematical sources used are present under literature/stacks-project/.

## Repair and comparison with current repository

The sandbox was empty on this retry, so I copied the current returned node rather than inventing a previous sandbox history. The released stage-1 repair note explicitly reopens the reviewed node with keep_plan=true. The initial required dry run exited because report.md was missing; no delivery process remained running. The repair now adds three comparable independent tasks, each with a self-contained statement and no proof, proof dependencies or proof origin. The parent's 4713-character six-step argument has been assigned in pairs to those tasks, with the final ascent/reflection application retained in the assembly. The report below retains every word of the old proof for their workers. Nothing was silently dropped or replaced by a restatement of the parent's base-change equality.

The item's existing statement, statement dependencies, Lean record, review metadata and ancestry are retained from the read-only current repository. No statement dispute was found: Tag 05VK has exactly a flat locally finitely presented source over S, locally finite type target over S, and arbitrary parameter base change. The latest blueprint (COMMITS.txt: main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345) changes the high-level direct-images proof (3) to compactification assembly, whereas inherited ancestry still records the old alteration prerequisite. This repair follows the explicit keep_plan instruction and does not change that higher route, chapter, unit, or target. blueprint_refs.py ancestor returns null, as it did for the returned node; I preserve it and prepend the item to each new via chain.

## Search and duplicate audit

I searched the whole DAG by flat locus, fibrewise flatness, compatible affine charts, residue-fibre comparison, and tags 05VJ, 05VK, 0399, 039C, 047C, 02FV. I read the matching statements, including the algebraic openness, affine-stalk/localization, finite-presentation cancellation, single-object fibre-of-base-change, pointwise flat-base-change and one-way fibre-criterion nodes. Whole-blueprint searches via blueprint_refs.py for flat locus, flatness, affine flat, residue fibre, fibrewise flatness and flatness criterion yielded no node stating any complete new statement. The polynomial-chart fibre criterion is restricted to polynomial targets and does not give the general S-scheme test. Project searches found only finiteness cancellation and single-family baseChange_fiber, not the three complete extractions.

For each new node I ran leanfinder in two phrasings, loogle, leansearch and a Mathlib grep via the required msearch.py command. All services answered. Queries and literal digest records are in the node and searches.jsonl. Flat.iff_flat_stalkMap and flat_appLE concern global flatness, finitePresentation_appLE assumes the finiteness already known, and UniversallyOpen.of_flat concerns openness of a map already flat. None gives the open flat-stalk chart locus. Flat.instFstScheme gives flatness of a pullback of an already flat map, but not the canonical simultaneous residue-fibre square; Pullback.Triplet tensor results concern point carriers instead. The fibre test is not Smooth.of_smooth_fiberToSpecResidueField, which assumes global flatness and proves smoothness. Thus all three are unsplit and zero are Mathlib leaves.

## Not duplicates

- lem-sfb-relative-flat-affine-charts vs lem-coef-infinity-local-adjoint-criterion: The existing statement constructs a coherent left adjoint from universal arrows in quasicategories; its 02FV is a Kerodon identifier, not the Stacks scheme lemma. It has no scheme charts or flatness assertion.
- lem-sfb-relative-flat-affine-charts vs lem-trf-flattening-ambient-module-preparation: The existing statement embeds a finite-type family into finitely presented affine-space opens and constructs pushed-forward modules for flattening. It assumes a qcqs base and a flat lfp restriction, and gives neither this compatible A to B to C chart package nor its pointwise flat-stalk locus.
- lem-sfb-relative-flat-affine-charts vs lem-sfb-flat-closed-family-ideal-base-change: The existing statement concerns a closed immersion between finitely presented families with flat closed source; it asserts exact pullback of the defining ideal sequence, not compatible affine charts or openness of a pointwise flat locus.
- lem-sfb-relative-flat-affine-charts vs lem-a1-map-over-base-finite-presentation: The existing statement gives local finite presentation of f and its source-open restrictions. It supplies cancellation but no compatible chart data, stalk-map identification, or open subset of Spec C identified with the flat stalk locus.
- lem-sfb-relative-flat-affine-charts vs lem-weil-pbc-descend-monomorphism: The existing statement descends monomorphy of a finite-type qcqs model along an affine-transition inverse limit. It has no chart-flatness or locus assertion.
- lem-sfb-relative-flat-fibre-test vs lem-sfb-fibrewise-flatness-criterion: The new node states both pointwise implications and permanence of the whole relative setup for every parameter scheme; the existing pointwise criterion states only the reverse implication and target flatness at one point. Shared source identifier(s): 039C.

- lem-sfb-relative-flat-affine-charts vs lem-weil-pbc-openness-of-flatness: the latter is about a module over two rings, and does not construct compatible scheme charts or identify their stalk maps.
- lem-sfb-flat-residue-fibre-square vs lem-weil-pbc-fibre-of-base-change: the latter compares one family and has no naturality square for an arbitrary map between two families or flatness conclusion for its projections.
- lem-sfb-flat-residue-fibre-square vs lem-sfb-pointwise-flatness-base-change: the latter assumes a cartesian scheme square and supplies flatness implications; it does not construct the residue-fibre square.
- lem-sfb-relative-flat-affine-charts vs lem-sfb-relative-flat-locus-base-change: the extraction gives chart data without any source flatness hypothesis and no parameter-base-change equality, rather than restating an item clause.
- lem-sfb-relative-flat-fibre-test vs lem-sfb-relative-flat-locus-base-change: the extraction gives a fibrewise local criterion with stability of hypotheses, with no openness or comparison between the loci over S and T.
- lem-sfb-flat-residue-fibre-square vs lem-sfb-relative-flat-locus-base-change: the extraction has no finiteness or relative source-flatness assumptions and concludes geometric compatibility and flat projections, not the locus equality.

## Review by Q83

I read more-morphisms.tex Tag 05VK (lemma-base-change-flatness-fibres) and its proof by Tag 05VJ (lemma-base-change-criterion-flatness-fibre), lines 4700–4777. The statement agrees with the structure-sheaf specialization, so there is no hypothesis correction. For the affine task I read morphisms.tex Tag 02FV (lemma-finite-presentation-permanence, lines 4275–4304) and more-morphisms.tex Tag 0399 (theorem-openness-flatness, lines 4445–4465), whose proof reduces to algebraic openness. The new statement keeps all three compatible charts, C finite presentation over A and B, openness on Spec C, and identification with the actual stalk map. It never identifies arbitrary affine intersections with affine schemes. Its handoff below takes a basic open in the intersection and gives the localization presentation explicitly. I opened the statements of finite-presentation-over-finite-type-algebra, openness-of-flatness, affine-open-stalk-localization and flat-over-localization: each supplies exactly the input named in the old steps, with finite-presentation hypotheses checked for B to C and the free rank-one C-module.

For the fibre-test task I read the non-Noetherian Tag 039C (theorem-criterion-flatness-fibre, lines 4590–4648), Tag 047C (lemma-flat-locus-base-change, lines 4468–4515) and the middle of the 05VJ proof. The structure-sheaf stalk is nonzero at every scheme point, satisfying 039C's explicit nonzero-module condition. The reverse implication uses source flatness; the forward implication is 047C(1), not a falsely reversed form of 039C. I opened the statements of flat-morphism-base-change, qcqs-morphism-permanence clause (3), and lft-base-change: they preserve respectively flatness of p, local finite presentation of p, and local finite type of q under every h. This is why the task's universal test assumes nothing on h. This task is the explicit re-split of old steps 3–4 requested by the human, rather than an unsolicited node for a one-line implication already supplied by the existing criterion.

For the residue-fibre task I read 05VJ's final displayed square and the assertion that its horizontal maps are flat. I opened fibre-of-base-change: it asserts the unique map commuting with both projections and the cartesian square for one family. Applying it separately to p and q, the two composites with each projection agree; the universal property then proves naturality of f_s and (f_T)_t and their cartesian square. I opened the residue-field definition, field-extension-base-change-faithfully-flat, faithfully-flat-ring-map, affine-spectrum and flat-morphism-base-change statements. They provide the field map, faithful flatness with D=K, flatness after forgetting faithfulness and the spectral/base-change implications used in the old final step. The handoff retains the maps a tensor b to ab and b to 1 tensor b, so the identification with the field extension is an actual isomorphism. No flatness of h is used or added.

Parent step 1 cites only lem-sfb-relative-flat-affine-charts; I read its statement and it really gives both the covering charts and the open sets equal to U intersect Z. Taking their union is elementary topology. Parent step 2 cites only lem-sfb-relative-flat-fibre-test; its statement gives both equivalences at the chosen points and the preserved hypotheses, rather than asking for an unrecorded universal version. Parent step 3 cites lem-sfb-flat-residue-fibre-square for the cartesian square, flatness of b and the projection identity, and lem-sfb-pointwise-flatness-base-change for its actual two implications. I checked that the point sent by a is the unique fibre point over pi_X(x'), so the criterion is applied to the correct stalk, not just an abstractly isomorphic fibre. The final set equality is extensionality. citations.json copies verbatim the statement of every cited node; there is no use of the proof of a cited node. All three parent steps are marked non-elementary because they apply these lemmas, and none exceeds 2000 characters. No off-unit new proof input is needed in this short assembly; the old unused algebra-openness tool declaration is removed from split_report.tool_uses, while the maintainer-owned tool_uses field is untouched.

I tested the new affine statement on the empty scheme, identity maps, and Spec k into the affine line over k: the last has a nonflat map and empty flat chart locus, showing the statement does not assume f itself flat. No noetherian base is needed by 00RC. I tested the fibre criterion on X=Y=S and on the closed immersion Spec k into Spec k[t] regarded over S=Spec k[t]: its fibre map at the origin is an identity but p is not flat, showing exactly why the task retains source flatness. For residue-fibre comparison, h an identity makes a and b identities; an empty fibre makes the square and flatness vacuous. An inseparable extension of fields remains flat, so no separability assumption was smuggled in. A nonflat h such as Spec k into Spec k[t] still has flat residue-field map, so the third task must not require h flat.

This repairs the only numbered return issue: all six old arguments now have assigned parallel tasks rather than only a shortened text. B1–B9 are met by statement-only self-contained TeX, definitions cited, exact source tags/labels and literal recorded searches. C1–C4 are checked against each actual statement as above, and no node depends on the parent as a mathematical dependency (created.item and blueprint.via are provenance only). D1–D2 are checked by the differing statements above; none asserts the original two-clause result. E1–E5 are checked by the source-flatness, arbitrary-base, basic-open, stalk and projection checks just described. No statement was silently weakened and no SGA source, compiler, Lake command, or project write was used.

## Preserved proof handoff for the three tasks

These are the returned proof's exact six texts, retained as work instructions only. New node JSON files contain statements and empty proofs. Workers may reuse the cited existing nodes rather than create duplicates. The assignments are: old 1–2 to lem-sfb-relative-flat-affine-charts, old 3–4 to lem-sfb-relative-flat-fibre-test, old 5–6 to lem-sfb-flat-residue-fibre-square; the pointwise theorem application at the end of 6 also appears explicitly in the parent's step 3.

### Returned step 1

Fix $x\in X$. By local finite presentation of $p$, take affine opens $W=\operatorname{Spec}A\subset S$ and $Z_0=\operatorname{Spec}C_0\subset p^{-1}(W)$ containing $p(x)$ and $x$, with $C_0$ finitely presented over $A$. By local finite type of $q$, choose an affine member $V=\operatorname{Spec}B$ of its finite-type chart cover of $q^{-1}(W)$ containing $f(x)$; thus $B$ is of finite type over $A$. Choose a basic open $Z=D(c)\subset Z_0\cap f^{-1}(V)$ containing $x$. Its ring $C=(C_0)_c$ is finitely presented over $A$: if $C_0=A[u_1,\ldots,u_n]/(r_1,\ldots,r_m)$ and $c$ is represented by $a(u)$, then $C=A[u_1,\ldots,u_n,v]/(r_1,\ldots,r_m,a(u)v-1)$. Apply finite presentation over an intermediate finite-type algebra to $A\to B\to C$. It gives finite presentation of $C$ over $B$. These charts around every $x$ show that $f$ is locally of finite presentation.

Existing inputs: def-sbc-locally-finite-presentation, def-weil-finite-type-morphism, lem-weil-pbc-finite-presentation-over-finite-type-algebra.

Source: literature/stacks-project/more-morphisms.tex, Tag 05VJ, proof, first sentence; Tag 02FV (morphisms-lemma-finite-presentation-permanence), affine argument.

### Returned step 2

On each affine chart $Z=\operatorname{Spec}C\to V=\operatorname{Spec}B$ just obtained, apply openness of the algebraic flat locus to $B\to C$ and the $C$-module $M=C$, which is finitely presented as a module since it is free of rank one. It gives an open set $E=\{\mathfrak r\in\operatorname{Spec}C:C_{\mathfrak r}\text{ is flat over }B\}$. For $z\in Z$ corresponding to $\mathfrak r$ and $f(z)$ corresponding to $\mathfrak b\subset B$, the affine-open stalk localization theorem identifies the structural stalk map with $B_{\mathfrak b}\to C_{\mathfrak r}$: on a fraction $b/u$ it is the image of $b$ times the inverse of the image of $u$, because both maps extend the section map on $B$. Flatness over a localization identifies flatness of $C_{\mathfrak r}$ over $B_{\mathfrak b}$ with flatness over $B$. Thus $E=U\cap Z$. These charts cover $X$, and their open subsets $E$ have union $U$, proving openness.

Existing inputs: lem-weil-pbc-openness-of-flatness, lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-flat-over-localization, def-weil-flat-morphism.

Source: literature/stacks-project/more-morphisms.tex, Tag 05VJ, proof, openness sentence, expanded on affine charts using Tag 00RC and Tag 00HT(2); Tag 0399 is not taken as a black box.

### Returned step 3

Fix $x\in X$ and put $s=p(x)$. The fibre projection identifies the points of $X_s$ with the points of $X$ above $s$. The square $X_s\to X$ over $Y_s\to Y$ is cartesian: a pair of maps to $X$ and $Y_s$ agreeing over $Y$ is exactly a map to $X$ together with a map to $\operatorname{Spec}\kappa(s)$ agreeing over $S$, by $qf=p$. The forward pointwise base-change assertion therefore gives: if $f$ is flat at $x$, then $f_s$ is flat at the corresponding point. Conversely $p$ is flat at $x$ by hypothesis, so the pointwise fibre criterion applied to $f$ gives flatness of $f$ at $x$ whenever $f_s$ is flat there. Consequently $x\in U$ if and only if $f_s$ is flat at the corresponding point of $X_s$.

Existing inputs: def-pc-scheme-fibre, def-pc-fibre-product, lem-sfb-pointwise-flatness-base-change, lem-sfb-fibrewise-flatness-criterion.

Source: literature/stacks-project/more-morphisms.tex, Tag 05VJ, proof, fibrewise description of U; Tag 039C and Tag 047C(1).

### Returned step 4

Let $h:T\to S$ be arbitrary, and write $p_T:X_T\to T$ and $q_T:Y_T\to T$. Base-change stability gives flatness of $p_T$, local finite presentation of $p_T$, and local finite type of $q_T$. Apply exactly the two pointwise implications of the preceding step to $f_T$ over $T$: at $x\prime\in X_T$ over $t\in T$, flatness of $f_T$ implies flatness of $(f_T)_t$ by pointwise base change, while flatness of $(f_T)_t$ implies flatness of $f_T$ by the fibre criterion since $p_T$ is flat. Hence $f_T$ is flat at $x\prime$ if and only if $(f_T)_t$ is flat at its corresponding fibre point. There is no restriction on $T$ or $h$.

Existing inputs: lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-lft-base-change, lem-sfb-pointwise-flatness-base-change, lem-sfb-fibrewise-flatness-criterion.

Source: literature/stacks-project/more-morphisms.tex, Tag 05VJ, proof, sentence that the hypotheses remain in force after arbitrary parameter base change; Tags 01U9, 01TS and 01T4.

### Returned step 5

For $x\prime\in X_T$ put $t=p_T(x\prime)$, $x=\pi_X(x\prime)$ and $s=h(t)=p(x)$. The map on residue fields makes $\kappa(t)$ a field extension of $\kappa(s)$. Applying the fibre-of-base-change theorem to both $p$ and $q$ identifies $(X_T)_t$ and $(Y_T)_t$ with $X_s\times_{\operatorname{Spec}\kappa(s)}\operatorname{Spec}\kappa(t)$ and $Y_s\times_{\operatorname{Spec}\kappa(s)}\operatorname{Spec}\kappa(t)$, respectively. These identifications commute with $f_s$ and $(f_T)_t$: their composites with each projection agree, so uniqueness in the fibre-product universal property proves equality. The square with vertical maps $(f_T)_t,f_s$ and these horizontal projections is therefore cartesian.

Existing inputs: def-weil-residue-field, lem-weil-pbc-fibre-of-base-change, def-pc-fibre-product.

Source: literature/stacks-project/more-morphisms.tex, Tag 05VJ, proof, final displayed fibre square; fibre products and their projection compatibilities.

### Returned step 6

The field-extension flatness theorem with $K=\kappa(s)$, $K\prime=\kappa(t)$ and $D=K$ says that $K\to K\otimes_K K\prime$ is faithfully flat. The isomorphism $K\otimes_K K\prime\to K\prime$, $a\otimes b\mapsto ab$, has inverse $b\mapsto1\otimes b$, so $K\to K\prime$ is flat. The unique stalks of their spectra are these fields; by the definition of flatness, $\operatorname{Spec}K\prime\to\operatorname{Spec}K$ is flat. Its base change $b:(Y_T)_t\to Y_s$ is flat. At our chosen fibre point the pointwise base-change lemma in the square of step 5 gives both implications: flatness of $f_s$ at $x$ implies flatness of $(f_T)_t$ at $x\prime$, and flatness of $(f_T)_t$ at $x\prime$ implies flatness of $f_s$ at $x$, since $b$ is flat at its image. Combining the fibrewise descriptions in steps 3 and 4 gives $x\prime\in\operatorname{Flat}(f_T)\iff x\in U$. Since $x\prime$ was arbitrary, $\operatorname{Flat}(f_T)=\pi_X^{-1}(U)$.

Existing inputs: lem-weil-pbc-field-extension-base-change-faithfully-flat, def-weil-pbc-faithfully-flat-ring-map, def-weil-affine-spectrum, def-weil-flat-morphism, lem-weil-pbc-flat-morphism-base-change, lem-sfb-pointwise-flatness-base-change.

Source: literature/stacks-project/more-morphisms.tex, Tag 05VJ, proof, final paragraph using Tag 047C and flatness of the residue-field extension; Tag 05VK is its structure-sheaf specialization.

## Unfinished work

The three new lemmas intentionally remain unsplit for other stage-1 workers. No requested repair remains unassigned. Final server dry-run and delivery results are recorded below after the commands finish.

## Validation

The required server dry run exited 0: OK (not pushed) deliver/Q83/lem-sfb-relative-flat-locus-base-change at 3c8c5785982: preflight passed. The server saved the durable receipt. I then read each source-tag collision statement and made its non-duplication explanation specific (including the unrelated Kerodon 02FV identifier). Delivery performs the final checks again.
