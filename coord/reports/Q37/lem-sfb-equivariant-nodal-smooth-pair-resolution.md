# Q37 stage-1 repair: lem-sfb-equivariant-nodal-smooth-pair-resolution

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-nodal-smooth-pair-resolution.json: parent split; statement unchanged; short seven-step assembly.
- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-birational-base-change-geometry.json: statement; status unsplit; searched in Mathlib, no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-marked-nodal-relative-log-charts.json: statement; status unsplit; searched in Mathlib, no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-log-smooth-fan-regularization.json: statement; status unsplit; searched in Mathlib, no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-nc-maximal-branch-strictification.json: statement; status unsplit; searched in Mathlib, no match.
- citations.json: verbatim statements for each citation of each parent step.
- report.md: review, search decisions, and full preservation of the returned proof.

## Attachments

None. The WeilConjectures search by blueprint tag and by nodal/equivariant resolution found no exact project declaration. The current Sheaf declaration exists_equivariant_nodal_smooth_pair_resolution ends in sorry; it is not an attachment. No Lean was written or compiled.

## WANTED

WANTED: Vidal (2004b), Proposition 4.4.4 and the following remark, for lem-sfb-equivariant-nodal-smooth-pair-resolution. This was already wanted in the returned source. The available ILO X Lemma 2.2 p.149 explicitly states the smooth-pair-over-a-field replacement, and VI/VIII supply the actual chart and blowup arguments. No SGA source is used.

## Return repaired

The return requests at least four independent statement-only nodes and a parent assembly of at most 3000 characters. The four work packets contain the three-step blocks 1--3 (2445 characters), 4--6 (2234), 7--9 (2747), and 10--12 (2989) of the old argument. They have their own objects, hypotheses, intermediate conclusions and logged searches; proof and proof_deps are empty and proof_origin is null. No new node states the whole resolution theorem. The parent statement is byte-for-byte unchanged. Its assembly is 2237 characters. Step 15 base-change conclusions are included in the first packet; the parameter and finite-projective-space arguments remain in parent steps 6--7 with their existing tool citations.

The starting sandbox contained only dispatcher marker files, not a prior split, report, citations or search log. I copied the current returned node from the read-only repository and retained its full contents as returned-node.json before editing. deliver.py overlays the worker-owned fields on current server main; maintainer metadata is left to that tool.

## Review by Q37

I read GOAL.md, the worker brief, stage 1, SETUP three-level authority, the chapter and unit, and both copies of delivery-errors B--E. I checked the local source of the parent theorem: its long statement is present with sorry, so it cannot close this item. I read the current blueprint direct-images proof (3); this repair keeps its alteration/finiteness subargument and the exact parent conclusion, and changes no chapter, unit or target. The new claims are intermediate base-change, logarithmic, fan, and strictification facts rather than replacements for the alteration route.

For the item I read ILO X Lemma 2.2, printed pp.149--150: successive equivariant modifications of each nodal curve and the explicit smooth-pair-over-a-field remark. For the first new node I also read Stacks 02V6 (morphisms.tex, lemma-base-change-projective) and 0C5B (curves.tex, lemma-base-change-nodal-family), including the Sym/base-change argument. The affine flatness argument proves integrality and density without a normal base or a reduction of W. The generic point is preserved by birational t. Finite-type-over-a-field, not separatedness, supplies Noetherian and qcqs bases. The first node also states precisely the projectivity, birationality and surjectivity of q needed at the end.

For the second new node I read ILO VI 1.4--1.9, pp.69--71. Proposition 1.9 in the source really asserts log smoothness, although lem-trf-nodal-log-regularity only states its log-regularity part. I did not take the missing clause from that narrower node. The new statement explicitly includes the R to Q chart, injective group map with cokernel Z, etale comparison, marked-coordinate case and recovery of the divisorial structure. The marking consists of disjoint sections in a smooth relative curve, so its single equation is a nonzerodivisor; the finite union is Cartier and etale over the base. No smoothness is inferred just from regularity over an imperfect field.

For the third new node I read VIII 3.3.13--3.3.15, pp.108--110 and 3.4.4--3.4.9, pp.110--112, then 4.1.1. I opened the four fan/descent cited node statements: the local-comparison node gives the localized fan isomorphism, the functorial fan node preserves centers and order, and the descent node requires composition and finite-disjoint-union compatibility. All are part of this work packet, not hidden in the parent. Sharp saturated characteristic groups are torsion free. The normalized blowups are taken along actual descended coherent ideals. Since the schemes are integral and finite type over F, the normalization node gives finite surjective birational normalization; finite-projective-bundle and projective-bundle-composition apply on the Noetherian targets. The output requires free characteristic monoids, log smoothness over F and smooth relative coordinate boundary charts, not just regularity. Automorphism compatibility yields semilinear J-equivariance with the group law.

For the fourth new node I read VIII 4.1.2--4.1.8, pp.117--118, and the coordinate computation of 4.2.8--4.2.9, pp.120--121. I checked the statements of maximal-branch blowup, permissible-boundary preservation, flat blowup comparison and affine blowup cover. The induction keeps old strict transform D_i and accumulated H_i distinct, with B_i=D_i union H_i. The maximal branch count drops, while H_i stays strict. In the explicit z_j-chart the reduced equation is the product written in the new statement; smooth flat base change makes every stratum smooth over F itself. Centers are intrinsic and invariant, and the Rees-algebra action respects multiplication. The Cartier m_i=1 identity blowup still removes the old strict transform and puts that component into H_{i+1}.

During the final interface audit I made the fan-regularization output explicitly allow charts with every boundary coordinate passing through the point, exactly as the relative NC criterion permits; this is the hypothesis used by the strictification statement. I also spelled out Noetherian as locally Noetherian and quasi-compact and cited pqf-def-locnoeth in all four new nodes.

Parent citation checks, step by step:

1. The first new statement gives every base-change property named here, including integral Noetherian total spaces, the generic fibre, preserved marking and equivariant B. Its hypotheses are exactly the parent curve and base-change hypotheses; smooth SNC for E is only needed next.
2. The second new statement applies to g because step 1 supplies properness, flat finite presentation, Noetherian finite type, nodal one-dimensional fibres and the marking. Parent hE supplies the smooth SNC base. Its own statement gives dense U and both log structures and log smoothness over F; B is the same support by |E|=t^{-1}D.
3. The third new statement applies with X=W, B as above and the diagonal action. It explicitly supplies projectivity, birationality, complement isomorphism, smoothness and coordinate boundary charts. No separatedness assumption is introduced.
4. The fourth new statement applies to the output pair in step 3, whose coordinate charts satisfy its exact hypotheses. It supplies all claimed properties of b, T-prime and E-prime. These are partial-stage results: it starts with an already smooth NC pair, not the nodal singular total space of the parent.
5. I opened lem-sfb-projective-bundle-composition: its target must be qcqs, which step 1 supplies for W,T,S0. I opened lem-trf-projective-bundle-proper and def-weil-proper-morphism: proper really means universally closed, so the closed image containing dense U proves surjectivity. Birationality of qr follows on the intersection of the dense opens for r and q; reduced inverse-image supports and the composed actions are elementary identities.
6. I opened lem-sfb-snc-boundary-parameter-criterion and lem-trf-regular-local-ufd-boundary-factorization. The first gives product equations in the ordinary local ring, the second makes each chosen parameter prime; together they give the individual reduced component ideals. I also read Stacks 0BI9/0BIA and ILO VIII 4.2.2(i); the ambient scheme is regular Noetherian as required.
7. I opened lem-weil-pbc-projective-ample-invertible (closed immersion into finite projective space over the field gives the ample line bundle), lem-trf-projective-bundle-to-h-projective (requires that ample bundle on the base), and lem-trf-h-projective-composition. This preserves the distinction between bundle-projective and H-projective, with no assumption of a global projective-space embedding for the original nonprojective base.

I checked small cases: empty D forces g smooth everywhere after base change; empty marking has unit Cartier ideal; empty total boundary admits length-zero towers; a smooth family with t the identity keeps its original integral generic fibre. A reducible special nodal fibre is permitted, so Mathlib total geometric integrality cannot be assumed. For uv equal to a product of several boundary coordinates the singular total space is permitted before fan regularization; the regularization statement cannot be replaced by smoothness of the fibres. Over F_p(t), regularity alone would not make a boundary like V(x^p-t) smooth, and our relative-chart hypotheses exclude that case. A self-intersecting global NC component is permitted before strictification, while the final components and intersections must be smooth. The m=1 case and the empty-boundary case meet the stated stopping rule. The group may permute markings and act on F; all towers use preserved unions and equivariance, without tameness or F-linearity.

Against B--E: each new statement introduces its objects and meanings, cites its definition nodes, has genuine single-backslash TeX, no proof sketch or proof dependencies, explicit source places, blueprint origin and three search kinds plus a second semantic phrasing. I checked all parent uses against their statements, and citations.json contains the exact relevant statement text. The proof-dependency union is exact; none of the new nodes depends on the parent or on another resolution theorem, so the split does not create a cycle. There is no elementary one-line lemma manufactured as a node: the four work packets contain the substantive arguments identified in the return. No parent step exceeds 2000 characters. All original work is preserved below; I did not shorten an argument to evade the re-split.

## Not duplicates

lem-sfb-nodal-birational-base-change-geometry vs def-trf-nodal-geometric-fibres: the new node packages marked nodal birational base change with integral total spaces, dense generic fibres and projective birational surjective q; the existing node is Nonempty connected one-dimensional nodal geometric fibres and does not state that combined intermediate geometry.
lem-sfb-nodal-birational-base-change-geometry vs lem-trf-nodal-family-fitting-singular: the new node packages marked nodal birational base change with integral total spaces, dense generic fibres and projective birational surjective q; the existing node is Fitting singular subscheme of a nodal relative curve and does not state that combined intermediate geometry.
lem-sfb-nodal-birational-base-change-geometry vs lem-trf-projective-nodal-family-geometry: the new node packages marked nodal birational base change with integral total spaces, dense generic fibres and projective birational surjective q; the existing node is Base change and the unramified singular subscheme of a nodal family and does not state that combined intermediate geometry.
lem-sfb-nodal-birational-base-change-geometry vs lem-trf-semistable-marked-base-change: the new node packages marked nodal birational base change with integral total spaces, dense generic fibres and projective birational surjective q; the existing node is Arbitrary base change of semistable marked curves and fibrewise stability and does not state that combined intermediate geometry.
lem-sfb-marked-nodal-relative-log-charts vs lem-trf-nodal-log-regularity: existing statement concludes log regularity only; new statement includes log smoothness over both the base pair and F, section Cartier property and all three chart cases.
lem-sfb-equivariant-log-smooth-fan-regularization vs lem-trf-monoidal-resolution-tower: existing statement only yields free monoids, without equivariance, projectivity, normalized-blowup geometry or F-smooth charts.
lem-sfb-equivariant-log-smooth-fan-regularization vs lem-per-gabber-log-blowup-regularization: existing statement assumes a separated scheme and gives regularity; new statement covers nonseparated finite-type F-schemes and preserves relative log smoothness to obtain smooth F-charts.
lem-sfb-equivariant-log-smooth-fan-regularization vs lem-per-log-regular-projective-log-resolution: existing statement requires quasi-projectivity over an excellent affine base and does not give the automorphism/fan-center comparisons or relative smooth chart conclusion.
lem-sfb-relative-nc-maximal-branch-strictification vs lem-trf-normal-crossings-strictification: existing statement assumes F algebraically closed and gives properness; new statement works over arbitrary F, with explicit relative smooth blowup charts, invariant centers, projectivity and branch-count termination.
lem-sfb-relative-nc-maximal-branch-strictification vs lem-trf-nc-maximal-branch-blowup: existing statement is only a single blowup branch-drop claim; the new node is the relative-field induction and equivariant projective strictification, including H_i preservation.
lem-sfb-relative-nc-maximal-branch-strictification vs lem-trf-permissible-boundary-preservation: existing statement is the one-step absolute regular boundary preservation; the new node supplies relative F-smooth charts and the terminating equivariant tower.
lem-sfb-marked-nodal-relative-log-charts vs lem-trf-nodal-etale-chart: existing statement gives nodal scheme local forms, not the resulting log-smooth morphisms and divisorial chart identification.
lem-sfb-equivariant-log-smooth-fan-regularization vs lem-per-gabber-absolute-equivariant-modification: existing statement assumes separatedness, quasi-excellence, tame generically free actions and performs further inertia modifications; the new node only performs fan regularization of a log-smooth F-pair and has none of those action hypotheses.
lem-sfb-equivariant-nodal-smooth-pair-resolution vs lem-per-split-nodal-relative-resolution-charts: existing statement assumes quasi-projectivity over an excellent affine base, a G-strict base boundary and smooth split fibre components and concludes special relative equations; this parent assumes the given smooth base modification over arbitrary F and keeps its previously reviewed statement unchanged.

I searched whole DAG statements for nodal/log smooth, fan/equivariance, generic fibre/integral/flat and strictification, and read the candidate statements above. Whole-blueprint search results are in dag-searches.txt. The ancestor command returns blueprint.from.node = None for this created chain; I preserve that value and carry the complete inherited via chain with the parent prepended for the new nodes.

## Mathlib search review

All four nodes have five searches executed by msearch.py (two distinct LeanFinder phrasings, Loogle, source grep, LeanSearch), exactly as recorded in searches.jsonl. Full results are preserved in the four *-hits.json files. All services answered. I read all returned signatures. Ordinary smoothness local presentations, generic relative normalization, Proj properness, analytic logarithms, integral ring maps, module projective resolutions and elliptic integral models do not state any new node. The Loogle candidate GeometricallyIntegral.isIntegral_of_isLocallyNoetherian at Mathlib/AlgebraicGeometry/Geometrically/Integral.lean:91 requires GeometricallyIntegral f (all fibres); the parent permits reducible special fibres and only its generic fibre is integral. No new node is a Mathlib leaf. Parent searches already exist in the copied node and were retained.

## Argument preservation and allocation

The following is the returned proof verbatim, not a replacement proof silently compressed. It is future-worker material in the report; new unsplit node files contain statements only. Each original paragraph is assigned below; old steps 13--15 retain their concluding work in the parent, with the q argument in the first new node as well.

### Returned step 1 -> lem-sfb-nodal-birational-base-change-geometry

Put $W=T\times_SS_0$, $g:W\to S_0$, $M_0=M\times_SS_0$, and $B=|M_0|\cup g^{-1}|E|$. The semistable marked base-change statement gives flatness, finite presentation, the one-dimensional nodal fibres, and the smooth-locus condition for $(W,M_0)$. Its geometric generic fibre is the original generic curve, since $t$ is birational. Projective-bundle properness gives finite type of $t$. Finite-type composition and base change, followed by the finite-type-over-Noetherian theorem, make $S,S_0,T,W$ Noetherian and finite type over $F$; a field is Noetherian since its only ideals are $0$ and $F$. In particular all later bases are quasi-compact and quasi-separated. The diagonal action of $J$ on the fibre product preserves $M_0$ and $B$.

Uses: lem-trf-semistable-marked-base-change, lem-sfb-finite-type-composition-base-change, lem-weil-pbc-finite-type-over-noetherian, lem-trf-projective-bundle-proper, def-weil-proper-morphism.
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X Lemma 2.2 proof p.149, one curve after modification of its base; Stacks 0C5B for nodal base change.

### Returned step 2 -> lem-sfb-nodal-birational-base-change-geometry

The projective-bundle convention is preserved by the base changes used here. Indeed, on affine charts $A\to A'$, for a finite-type module $N$ the canonical graded identity $A'\otimes_A\operatorname{Sym}_A N=\operatorname{Sym}_{A'}(A'\otimes_A N)$ identifies the corresponding projective bundles: their standard charts are the degree-zero parts after localization at a degree-one generator, and these same presentations commute with $A'\otimes_A-$. Finitely many generators of $N$ pull back to generators, and these chart identifications agree on intersections. Pull back the closed immersion defining a projective morphism and apply the cited closed-immersion base-change theorem. Thus both $g:W\to S_0$ and $q:W\to T$ are projective in precisely the required convention. In particular $g$ is proper by the projective-bundle properness theorem.

Uses: def-trf-projective-bundle-morphism, lem-weil-pbc-closed-immersion-base-change, lem-trf-projective-bundle-proper.
Source: literature/stacks-project/morphisms.tex, Stacks 02V6, morphisms-lemma-base-change-projective; affine graded-chart argument, then projective-bundle properness.

### Returned step 3 -> lem-sfb-nodal-birational-base-change-geometry

Both $T$ and $W$ are integral. Here is the flatness argument, applied with base $S$ and then $S_0$. For an affine open $\operatorname{Spec}A$ of the integral base, let $\operatorname{Spec}C$ be a nonempty affine open of its inverse image and $K=\operatorname{Frac}(A)$. Flatness makes $C\to C\otimes_AK$ injective: multiplication by every nonzero $a\in A$ is injective on $C$. The localization is nonzero and is the ring of a nonempty affine open of the integral generic curve, hence is a domain; therefore $C$ is a domain. Every nonempty open meets the generic fibre by the same localization argument. Two such opens meet because their intersections with the generic fibre meet. Thus the total space is reduced and irreducible. This also proves density of every inverse image of a dense open of the base. No reduction or choice of a main component of $W$ is needed.

Uses: .
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X Lemma 2.2 proof p.149, base change of one nodal curve; elementary affine flatness and generic-fibre argument.

### Returned step 4 -> lem-sfb-marked-nodal-relative-log-charts

Apply the relative normal-crossings chart criterion to $(S_0,E)$: its divisorial log structure is fs, log regular and log smooth over the trivial log scheme $\operatorname{Spec}F$. The marking $M_0$ is an effective Cartier divisor, finite etale over $S_0$. To check the only additional assertion, work in the relative smooth locus of $g$ and apply the smooth-pair coordinate theorem to one section $S_0\hookrightarrow W_{\mathrm{sm}}$ over $S_0$. Relative dimension one makes its equation a single coordinate $z=0$, a nonzerodivisor. Near that section avoid the other disjoint closed sections; off all sections the ideal is the unit ideal. Hence the finite union is Cartier. These arguments include empty $E$ or $M_0$.

Uses: lem-sfb-free-characteristic-relative-nc-criterion, lem-pur-smooth-pair-local-coordinates.
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VI 1.9 pp.70--71, marked smooth-locus case; X Lemma 2.2 p.149 relative-pair remark.

### Returned step 5 -> lem-sfb-marked-nodal-relative-log-charts

The hypotheses of the nodal log-regularity theorem now hold for $g$, base boundary $|E|$, and Cartier marking $M_0$: Step 2 supplies properness and Step 1 supplies flat finite presentation and the nodal fibres. It follows that $B$ is nowhere dense and $(W,B)$ is log regular, with its divisorial log structure. In particular its open complement $U=W\setminus B$ is dense. Notice that $B$ is exactly the pullback support of $|M|\cup f^{-1}D$, because $|E|=t^{-1}D$.

Uses: lem-trf-nodal-log-regularity.
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VI Proposition 1.9, pp.70--71.

### Returned step 6 -> lem-sfb-marked-nodal-relative-log-charts

We also need relative log smoothness, which is not a clause of the preceding cited node. Use the nodal-chart theorem: at a node the etale local equation is $uv=h$, with $h=\varepsilon\alpha(a)$ in an fs base chart $P$, and away from nodes the map is smooth or has the marked coordinate $z=0$. For a node use the divisorial-chart theorem with $R=\mathbf Z\oplus P$ and $Q=\mathbf N^2\amalg_{\mathbf N}R$. It identifies the comparison scheme with $uv=\varepsilon\alpha(a)$ and gives injective $R^{\rm gp}\to Q^{\rm gp}$ with cokernel $\mathbf Z$. The comparison from the nodal neighbourhood is etale, so the definition of log smoothness applies. At smooth unmarked points use $P\to P$; at marked points use $P\to P\oplus\mathbf N$ and the coordinate $z$. The log structure in each case is the divisorial one: log regularity and the recovery assertion of the injective-chart theorem identify it from the same triviality locus $U$. Thus $(W,B)\to(S_0,E)$ is log smooth. The composition theorem and Step 4 give log smoothness over the trivial log field $F$.

Uses: lem-trf-nodal-etale-chart, lem-trf-nodal-divisorial-chart, def-per-fs-log-smooth-etale, lem-trf-log-smooth-log-regular, lem-sfb-log-smooth-composition-strict-base-change.
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VI Proposition 1.9 proof p.71, cocartesian monoid square and its group cokernel; Stacks 0CBY is the nodal etale input.

### Returned step 7 -> lem-sfb-equivariant-log-smooth-fan-regularization

Construct the regularization tower directly from fan charts, without a separatedness assumption on $W$. Its sharp saturated characteristic monoids have torsion-free group completions: if $na=0$, saturation puts both $a$ and $-a$ in the monoid, so $a$ is a unit and hence zero. The fan-chart theorem gives strict etale neighbourhoods with saturated torsion-free fan charts. On any such chart $c:V\to F$, pull back the functorial saturated fan desingularization using the fan-chart blowup theorem. Its last characteristic monoids are free. For two charts of a strict comparison, the local-comparison theorem identifies the localized fans by an isomorphism. Fan functoriality for these localizations and isomorphisms identifies their contracted towers, retaining ordered centers. These comparisons respect composition and finite disjoint unions. Thus the hypotheses of log-blowup etale descent hold, and it gives a finite global tower $W_1\to W$ with free final characteristic monoids. Applying these comparisons to each automorphism of $(W,B)$ lifts $J$ to the tower; composition compatibility gives the group law. Everything here concerns log schemes and their automorphisms, so it also applies when $J$ acts nontrivially on $F$.

Uses: lem-trf-log-fan-chart-blowup, lem-trf-functorial-fan-desingularization, lem-trf-strict-fan-chart-local-comparison, lem-trf-functorial-log-blowup-etale-descent.
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII Theorems 3.3.15 and 3.4.9, pp.109--112, canonical log ideals and strict descent.

### Returned step 8 -> lem-sfb-equivariant-log-smooth-fan-regularization

Each global step of this tower is a normalized ordinary blowup along the finite-type nonzero ideal generated by its coherent log center, by the log-blowup normalization theorem. The ordinary blowup is integral and projective in the projective-bundle sense. It is finite type over $F$; its normalization in its function field is finite, surjective and birational by the finite-type normalization theorem. The finite map is projective in the projective-bundle sense, and projective-bundle composition applies because every base is Noetherian. Inductively the global composite $W_1\to W$ is projective and birational, and all its stages are integral finite-type schemes. This proves global projectivity from the actual descended ideals, rather than from local projectivity. The log-blowup theorem identifies its triviality locus with the inverse image of $U$ and gives an isomorphism there.

Uses: lem-trf-log-blowup-normalization, lem-sfb-integral-blowup-projective-geometry, lem-sfb-finite-type-composition-base-change, lem-sc-normalization-exists, lem-trf-finite-projective-bundle, lem-sfb-projective-bundle-composition.
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 3.4.5--3.4.9 pp.111--112; Stacks 02ND, 02NS, 035S, 0B3I and 0C4P for underlying projective morphisms.

### Returned step 9 -> lem-sfb-equivariant-log-smooth-fan-regularization

Saturated log blowups are log etale, so Step 6 and log-smooth composition show that $W_1$ is still log smooth over the trivial log field $F$. Step 8 preserves log regularity and Step 7 gives free characteristic monoids; the free-characteristic criterion for a log regular scheme therefore gives regularity of $W_1$. Applying the new relative chart criterion shows that $W_1$ is smooth over $F$ and that $B_1=(W_1\times_WB)_{\mathrm{red}}$ has smooth relative normal-crossings charts. This is the point where mere regularity would be insufficient over an imperfect field. We have not yet asserted strictness of the global components.

Uses: lem-sfb-log-smooth-composition-strict-base-change, lem-trf-free-characteristic-regular-boundary, lem-sfb-free-characteristic-relative-nc-criterion.
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 4.1.1 p.117, with X Lemma 2.2 p.149 relative-field refinement.

### Returned step 10 -> lem-sfb-relative-nc-maximal-branch-strictification

Strictify by the maximal-branch algorithm, retaining $D_i$, the strict transform of the original $B_1$, and $H_i$, the accumulated reduced exceptional boundary. Start with $D_0=B_1$, $H_0=\varnothing$. Inductively the full boundary is $D_i\cup H_i$, is normal crossings, and $H_i$ is strict normal crossings. If $D_i$ is nonempty, its geometric branch count has a finite positive maximum $m_i$. The maximal-branch blowup theorem gives the reduced closed locus $Z_i$ where this maximum is reached; it is regular and, in boundary coordinates, is $z_1=\cdots=z_{m_i}=0$, with $D_i$ given by $z_1\cdots z_{m_i}=0$. Its blowup has strict transform $D_{i+1}$ with branch count at most $m_i-1$. The center is invariant under every automorphism preserving $D_i$, since its definition uses only this intrinsic branch count. Consequently it is $J$-invariant.

Uses: lem-trf-nc-maximal-branch-blowup.
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 4.1.6--4.1.8 p.118, multiplicity-stratum algorithm.

### Returned step 11 -> lem-sfb-relative-nc-maximal-branch-strictification

These ordinary blowups preserve the relative smooth charts. In a chart of Step 9 the center is the inverse image of the coordinate ideal $(z_1,\ldots,z_m)$ under a smooth map to $\mathbf A^r_F$. Smooth maps are flat, so the flat blowup base-change theorem applies. Its standard $z_i$-chart has coordinates $z_i$, $v_j=z_j/z_i$ for $1\leq j\leq m$, $j\ne i$, and $z_k$ for $k>m$. The reduced full boundary is
$$z_i\prod_{1\leq j\leq m,\ j\ne i}v_j\prod_{m<k\leq r}z_k=0.$$
This chart is affine space over $F$ with its coordinate boundary, and the pulled-back chart maps smoothly to it. Every coordinate intersection remains smooth of the expected codimension. The affine blowup charts cover, and smoothness is preserved by their base changes and composition, so the assertion holds globally at every stage. Thus the relative smoothness is checked over $F$ itself, without descending regularity from an algebraic closure.

Uses: lem-pc-smooth-flat, def-nagata-blowup-flat-base-change-map, thm-nagata-blowup-flat-base-change, prop-nagata-affine-blowup-chart-cover, lem-sbc-smooth-relative-dimension-permanence, lem-sfb-free-characteristic-relative-nc-criterion.
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 4.2.8--4.2.9 pp.120--121, coordinate blowup calculation over F; flat base change via the named comparison theorem.

### Returned step 12 -> lem-sfb-relative-nc-maximal-branch-strictification

Apply permissible-boundary preservation at each step to $B_i=D_i\cup H_i$, $H_i$ and $Z_i$. Its exact conclusions give the normal-crossings full boundary and strictness of $H_{i+1}=(b_i^{-1}(H_i\cup Z_i))_{\mathrm{red}}$, together with $B_{i+1}=D_{i+1}\cup H_{i+1}$. This closes the induction in Step 10; the relative charts in Step 11 make all its regular strata smooth over $F$. After at most $m_0$ iterations $D_i$ is empty, since the positive maximum strictly decreases. The final reduced full boundary is therefore $H_i$, a relative strict normal crossings divisor: locally each of its distinct global components is a single coordinate branch, and their intersections are precisely coordinate intersections. If $m_i=1$, the center is Cartier and its blowup can be the identity, but its old strict transform is empty and that divisor is included in $H_{i+1}$; the same decrease still holds. If $B_1$ is empty, the tower has length zero. Each blowup is integral and projective by the ordinary-blowup theorem, and is an isomorphism off its center. Its action is induced on the Rees algebra by the invariant center, with group multiplication inherited degreewise. Hence the whole strictification tower is $J$-equivariant.

Uses: lem-trf-permissible-boundary-preservation, lem-sfb-integral-blowup-projective-geometry, thm-nagata-global-blowup-complement.
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, VIII 4.1.4--4.1.8 pp.117--118, termination and equivariance, and 4.2.9 p.121.

### Returned step 13 -> parent step 5

Let $T'$ be the last scheme and $r:T'\to W$ the composite of both towers. Projective-bundle composition makes $r$ projective, and projective-bundle properness makes it closed. It is birational because each step is an isomorphism over the same dense $U$, with unchanged function field; it is surjective because its closed image contains dense $U$. It is $J$-equivariant by Steps 7 and 12, and Step 11 gives smoothness over $F$. Every step changes the boundary to its reduced total inverse image, so the final boundary $E'$ is exactly $(r^{-1}B)_{\mathrm{red}}$. The log-blowup and ordinary-blowup complement statements show that $r$ is an isomorphism outside $B$. These prove the asserted support and complement clauses, including when both markings and boundary are empty.

Uses: lem-sfb-projective-bundle-composition, lem-trf-projective-bundle-proper, def-weil-proper-morphism.
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X Lemma 2.2 proof p.149, composition of the one-curve modifications; VIII 4.1.1--4.1.8.

### Returned step 14 -> parent step 6

The regularity already obtained and the strict boundary supplied by Step 12 satisfy the strict-boundary parameter criterion. At $x\in T'$ its ideal is $(t_1\cdots t_s)$ for distinct members of a regular system of parameters of $\mathcal O_{T',x}$. The regular-local factorization theorem makes each $t_i$ prime. Consequently the reduced union defined by this product has as its components through $x$ exactly the distinct height-one ideals $(t_i)$; thus each component has the required individual local equation. This is an assertion in the ordinary local ring, not only the strict henselization. All local rings are regular by the earlier regularization and permissible-boundary preservation conclusions.

Uses: lem-sfb-snc-boundary-parameter-criterion, lem-trf-regular-local-ufd-boundary-factorization.
Source: literature/stacks-project/etale.tex, Stacks 0BIA, etale-lemma-strict-normal-crossings; VIII Remark 4.2.2(i) p.118.

### Returned step 15 -> lem-sfb-nodal-birational-base-change-geometry (q geometry) and parent steps 5,7 (composition and H-projectivity)

Finally $q:W\to T$ is the base change of the projective birational surjection $t$. By Step 2 it is projective. Choose a dense open $V\subseteq S$ over which $t$ is an isomorphism; $f^{-1}V$ is dense in integral $T$ by Step 3. Over this open $q$ is an isomorphism, so it is birational; its image is closed by projective-bundle properness and contains this dense open, hence it is surjective. Composition with $r$ gives all three assertions for $T'\to T$, with the same function field. If $S_0$ embeds into finite-dimensional projective space over $F$, the cited ample-sheaf theorem gives an ample invertible sheaf on $S_0$. The projective-bundle morphism $T'\to S_0$ is then H-projective by the conversion theorem. Its composite with the H-projective structure map $S_0\to\operatorname{Spec}F$ is H-projective by H-projective composition. This proves the final finite-projective-space clause, without conflating the two projectivity conventions.

Uses: lem-trf-projective-bundle-proper, def-weil-proper-morphism, lem-sfb-projective-bundle-composition, lem-weil-pbc-projective-ample-invertible, lem-trf-projective-bundle-to-h-projective, lem-trf-h-projective-composition.
Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X Lemma 2.2 p.149, projectivity and composition; Stacks 087S and 01WE for the final convention change.

## Unfinished work

The four new statements are deliberately unsplit so independent workers can prove their separate arguments. No requested repair point remains unaddressed. This stage-1 delivery makes no Lean changes.

## Validation

Required dry run completed successfully: deliver.py Q37 lem-sfb-equivariant-nodal-smooth-pair-resolution --no-push exited 0 and printed OK (not pushed) at 88828bae031: preflight passed. The delivery invokes the server preflight, check_dag and review_split. Local noncompiler checks also verified all 15 original proof texts retained verbatim, the unchanged parent statement, four unsplit nodes with empty proof/dependency lists, complete citation quotes, and the 2237-character assembly. No compiler, Lake or local server-only checker was run.
