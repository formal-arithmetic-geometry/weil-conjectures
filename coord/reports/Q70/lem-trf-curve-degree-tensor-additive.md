# Repair report: lem-trf-curve-degree-tensor-additive

## Files written

- dag/nodes/sec-trace-formula/lem-trf-curve-degree-tensor-additive.json: statement unchanged; four short assembly steps; status split.
- dag/nodes/sec-trace-formula/lem-trf-proper-field-invertible-coherent.json: statement, unsplit; Mathlib searches found no coherence theorem for these module sheaves.
- dag/nodes/sec-trace-formula/lem-trf-curve-pullback-tensor-euler.json: statement, unsplit; Mathlib searches found no proper-curve coherent Euler increment.
- citations.json: verbatim statement quotations for every use of every parent step.

## Attachments

None. The live WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean:645 degree_tensorObj requires SmoothOfRelativeDimension 1, from lines 249-250. It cannot attach to a theorem allowing singular and nonreduced schemes of dimension at most one. The exact Sheaf/AlgebraicGeometry/CurveDegreeTensorAdditive.lean declaration is still sorry. The new preparation's generic coherence theorem exists in the project, not Mathlib, but does not itself include the proper-field Noetherian preparation.

## WANTED

None. All sources used are available locally. No SGA source used.

## What was wrong and what changed

The human return asks to redistribute the 3464-character proof into at least two comparable independent tasks. The sandbox initially contained only dispatcher marker files, no retained JSON, report or search log; the required initial dry run exited with “no node files”. I copied the current repository item, which contains exactly the four returned arguments and the prior review corrections. The statement and Lean records are preserved. This is a substantive extraction into two statement-only nodes, not an unchanged re-push. Their proofs are deliberately left for future workers. The Noetherianity/coherence preparation and the generic-rank/pullback Euler argument carry the old Step 1 (843 characters) and most of old Step 3 (1283 characters), respectively. Neither new node states additivity on all proper dimension-at-most-one schemes. The weighted reduction and finite-sum calculation stay in the parent.

## Review by Q70

I read Stacks varieties.tex, lemma-degree-tensor-product (0AYX), lemma-degree-on-proper-curve (0AYV), and lemma-degree-in-terms-of-components (0AYW), including the generic multiplicity paragraph. I also read coherent.tex lemma-coherent-Noetherian (01XZ), morphisms.tex lemma-finite-type-noetherian (01T6), and modules.tex tensor-pullback and invertible-construction statements (01CD, 01CT). These are the same route as the returned proof. The fixed chapter and curve-zero unit remain untouched; the inherited distant blueprint ancestry is retained and refined with exact returned-step places rather than claiming that the current ancestor's contracting-correspondence proof contains a curve-degree theorem.

For parent Step 1 I opened the new preparation statement: it explicitly supplies Noetherianity and coherence on any proper field scheme. I opened lem-weil-pbc-invertible-pullback-tensor: clause (1), with the identity map, really supplies tensor invertibility. Step 2 cites the statement of lem-trf-degree-weighted-irreducible-components, not its proof: it supplies the same components, proper integral dimension-one hypotheses, finite positive weights defined from X, the formula, and the zero-dimensional/empty case. For Step 3, that component statement supplies properness, integrality and dimension exactly one; invertible-pullback-tensor clause (1) supplies both invertible pullbacks; the new preparation supplies the coherent second pullback required by the new Euler node. The new Euler node states exactly the characteristic identity used, already for the pullback of the original tensor. Subtracting chi(O) is justified by the degree definition whose statement I read. Thus no unproved comparison is hidden in the parent. Step 4 only distributes an integer finite sum and substitutes the three formulas. Every parent use has a verbatim quotation in citations.json.

The preparation node has no dimension hypothesis: a proper k-scheme is finite type, Spec k is Noetherian, and 01T6 then supplies Noetherianity; local rank-one trivializations give finite type and quasi-coherence, so 01XZ applies. The structure sheaf satisfies the same local condition. The second new node assumes coherence of j^*M explicitly so the two tasks can be worked independently. Its generic rank is one because a local generator remains a generator in the generic stalk, whose ring is the function field; 0AYV applies. The 01CD comparison is valid for arbitrary morphisms, with no flatness. Isomorphic sheaves give inverse maps on cohomology and equal dimensions; this supplies the Euler transport. It is essential that the comparison be between j^*(L tensor M) and j^*L tensor j^*M, not a claim about flatness of a component immersion.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the files: new nodes introduce all their objects, cite their notions, have no proof or proof_deps, and carry sources and blueprint ancestry. The self-contained smaller tasks are precisely the arguments the human asked to extract; the parent conclusion and all original edge cases are kept. No circular reference is introduced: the new nodes have only definition statement dependencies. Generic off-unit tensor/pullback use is declared in split_report, preserving the accepted route. No long parent step exceeds 2000 characters; the whole parent is under 3000.

Small cases: the preparation permits the empty scheme and proper Artinian schemes, also a nonreduced curve. The Euler node requires a nonempty integral curve, so no nonexistent generic point is used on empty or zero-dimensional schemes. For P1 and identity j, L=O(a), M=O(b), the identity is a+b+1=a+(b+1). For a constant j with both pullbacks trivial it reads chi(O)=0+chi(O). Negative degrees and singular integral curves are admitted; no smoothness or algebraic closedness is used. For the parent, if there are no dimension-one components all three sums vanish, including the empty scheme. A doubled P1 has the same component formula with multiplicity two; embedded points are already accounted for in 0AYW and are not spuriously added.

## Preservation of the returned argument

The following records the full returned proof, to make the redistribution reviewable without relying on an unrecorded summary. Each numbered argument has a specific owner after repair.

### Returned Step 1

We first check the coherence hypothesis that will be used on each component. For any proper $k$-scheme $Y$, its structure map is of finite type [def-weil-proper-morphism]. The field $k$ is Noetherian: every ideal containing a nonzero element contains $1$ and is the whole ring; the zero ideal is generated by $0$ [def-weil-field, def-weil-pbc-noetherian-ring]. The one-point affine scheme $\operatorname{Spec}k$ has its whole space as an affine Noetherian cover and is quasi-compact [def-weil-affine-spectrum, pqf-def-locnoeth]. Thus [lem-weil-pbc-finite-type-over-noetherian] implies that $Y$ is Noetherian. An invertible module on $Y$ is quasi-coherent and locally generated by one element [def-sc-invertible-module], so [pqf-lem-coherent-ft-locnoeth] makes it coherent. This applies both to $X$ and to every proper integral component below.

Owner after repair: lem-trf-proper-field-invertible-coherent; the field ideals, affine Noetherian base, finite-type ascent and coherence steps all belong here.

### Returned Step 2

The product $\mathcal L\otimes\mathcal M$ [def-pur-sheaf-tensor-product] is an invertible $\mathcal O_X$-module [def-sc-invertible-module] by clause (1) of [lem-weil-pbc-invertible-pullback-tensor], applied with $f=\mathrm{id}_X$. Apply [lem-trf-degree-weighted-irreducible-components] to the three invertible modules $\mathcal L$, $\mathcal M$, and $\mathcal L\otimes\mathcal M$ on $X$. It supplies the same finite list of proper integral dimension-one schemes $C_i$ and the same finite weights $m_i$, determined by $X$, with
$$\deg_k(\mathcal L)=\sum_i m_i\deg_k(\mathcal L|_{C_i}),\quad \deg_k(\mathcal M)=\sum_i m_i\deg_k(\mathcal M|_{C_i}),\quad \deg_k(\mathcal L\otimes\mathcal M)=\sum_i m_i\deg_k((\mathcal L\otimes\mathcal M)|_{C_i}).$$
No contribution from an isolated zero-dimensional component or an embedded point is added: the cited formula already concerns all of $X$.

Owner after repair: Parent Step 2, with tensor invertibility in parent Step 1.

### Returned Step 3

Fix $i$ and put $L_i=\mathcal L|_{C_i}=j_i^*\mathcal L$ and $M_i=\mathcal M|_{C_i}=j_i^*\mathcal M$ for the closed immersion $j_i:C_i\to X$ [def-pc-module-pullback]. Clause (1) of [lem-weil-pbc-invertible-pullback-tensor] with $f=j_i$ shows that both are invertible [def-sc-invertible-module], and $M_i$ is coherent by Step 1. At the generic point its fibre is one-dimensional, so its generic rank is $1$. The hypotheses of [lem-trf-curve-euler-tensor-generic-rank] hold by Step 2, and that formula with $\mathcal L=L_i$, $\mathcal F=M_i$ gives $\chi(C_i,L_i\otimes M_i)=\deg_k(L_i)+\chi(C_i,M_i)$. Subtracting $\chi(C_i,\mathcal O_{C_i})$ and using [def-pc-degree-line-bundle] yields $\deg_k(L_i\otimes M_i)=\deg_k(L_i)+\deg_k(M_i)$. The tensor whose degree occurs in Step 2 identifies with this tensor: clause (2) of [lem-weil-pbc-invertible-pullback-tensor] with $f=j_i$ gives an isomorphism of $\mathcal O_{C_i}$-modules $(\mathcal L\otimes\mathcal M)|_{C_i}=j_i^*(\mathcal L\otimes\mathcal M)\cong j_i^*\mathcal L\otimes j_i^*\mathcal M=L_i\otimes M_i$ [def-pur-sheaf-tensor-product]; no flatness of $j_i$ is needed. Euler characteristics and hence degrees are unchanged by isomorphism, since the induced maps on every cohomology group are inverse [def-pc-euler-characteristic].

Owner after repair: lem-trf-curve-pullback-tensor-euler for pullback tensor comparison, generic rank one and the Euler formula; lem-trf-proper-field-invertible-coherent supplies coherence; parent Step 3 retains the degree subtraction.

### Returned Step 4

Substitute the component identity of Step 3 into the third sum in Step 2 and distribute the finite sum:
$$\deg_k(\mathcal L\otimes\mathcal M)=\sum_i m_i(\deg_k(L_i)+\deg_k(M_i))=\sum_i m_i\deg_k(L_i)+\sum_i m_i\deg_k(M_i)=\deg_k(\mathcal L)+\deg_k(\mathcal M).$$
All equalities are in $\mathbf Z$. If there are no dimension-one components, the three sums are empty and all three degrees are zero, so the same calculation applies, including $X=\varnothing$.

Owner after repair: Parent Step 4, verbatim.

## Search review

The item already carries the earlier real searches and they are preserved unchanged. For each new node I ran LeanSearch, Loogle, Mathlib grep and two LeanFinder phrasings through the mandatory msearch.py wrapper; searches.jsonl contains the actual records. The preparation hits were Noetherian predicates, affine-cover facts, finite generation and finite presentation, with no coherent invertible sheaf theorem; the second node's hits were tensor carriers of scheme fibre products, Picard multiplication over rings, incidence-algebra Euler characteristics and representation characters. None has the same objects and conclusion. No unavailable service was reported as a negative match. DAG and whole-blueprint searches included invertible coherent, coherent proper field, pullback Euler, tensor degree, Noetherian field, 01XZ and 0AYV; principal overlaps are distinguished below.

## Not duplicates

lem-trf-curve-pullback-tensor-euler vs lem-trf-curve-degree-tensor-additive: the item concludes an identity of degrees on arbitrary proper schemes of dimension at most one, including reducible and nonreduced schemes. The extracted task supplies an Euler-characteristic increment on a single integral proper curve for a tensor pulled back along an arbitrary morphism from another scheme. It isolates the former Step 3 generic-rank calculation and tensor comparison; it does not contain the weighted-component argument or finite-sum assembly. Its intended proof uses 0AYV and 01CD, never the parent additivity theorem, so there is no circular use. This extraction and the separate coherence task are the two arguments requested by the human re-split return, rather than a new name for the full item.

lem-trf-proper-field-invertible-coherent vs lem-pc-closed-structure-ambient-ideal-extension: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Ambient ideal-power extension from a closed structure module. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-pc-coherent-open-section-carrier: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Coherent carrier of an open section. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-pc-cokernel-finite-presentation-noetherian: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Finitely presented cokernels on locally Noetherian schemes. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-pc-m1-projective-pushforward-finite-type-independent: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Independent finite type of projective pushforward. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-pqf-kernel-finite-presentation-noetherian: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Finitely presented kernels on locally Noetherian schemes. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-pur-affine-line-support-geometry: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Finite-type and Noetherian geometry of the affine-line support pair. It does not state this combined proper-field preparation. Shared source tags: 01T6.

lem-trf-proper-field-invertible-coherent vs lem-pur-conormal-graded-algebra: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Conormal graded algebra on a closed subscheme. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-sbc-composite-fibre-local-models: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Local models of the fibres of a composite. It does not state this combined proper-field preparation. Shared source tags: 01T6.

lem-trf-proper-field-invertible-coherent vs lem-sc-affine-finite-module-free-locus: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Finite modules free at all primes are locally free on an affine cover. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-sc-coherent-affine-free-resolution: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Finite free resolution of a coherent sheaf on a Noetherian affine neighbourhood. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-trf-fibre-component-relative-associated: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Fibre-component generic points are relative associated points. It does not state this combined proper-field preparation. Shared source tags: 01T6.

lem-trf-proper-field-invertible-coherent vs lem-trf-proper-base-change-coherent-conservative: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Proper surjective base change is coherent and conservative on vanishing topoi. It does not state this combined proper-field preparation. Shared source tags: 01T6.

lem-trf-proper-field-invertible-coherent vs lem-weil-pbc-affine-coherent-tilde-presentation: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Associated-module presentation of a coherent sheaf on an affine scheme. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-weil-pbc-coherent-formal-modules-affine: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Coherent formal modules on an affine Noetherian scheme are finite modules over the completion. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-weil-pbc-coherent-integral-generic-ideal-sigma-coherent: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Coherence of finite coproducts of a coherent ideal. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-weil-pbc-coherent-stalk-map-extends: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states A map of stalks of coherent modules comes from a map on a neighbourhood. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-weil-pbc-finite-algebra-noetherian: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states A module-finite algebra over a Noetherian ring is Noetherian. It does not state this combined proper-field preparation. Shared source tags: 01T6.

lem-trf-proper-field-invertible-coherent vs lem-weil-pbc-finite-pushforward-coherent: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states The direct image of a coherent module along a finite morphism to a locally Noetherian scheme is coherent. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-weil-pbc-finite-structure-tensor-powers-supported: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Coherence and proper support of the tensor square and cube. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-weil-pbc-finite-structure-unit-quotient-system: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Compatible reduced units through a coherent proper supporting quotient. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-weil-pbc-finite-type-over-noetherian: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states A scheme of finite type over a Noetherian scheme is Noetherian (Stacks 01T6). It does not state this combined proper-field preparation. Shared source tags: 01T6.

lem-trf-proper-field-invertible-coherent vs lem-weil-pbc-formal-affine-morphism-realization: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Affine formal morphism realization. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs lem-weil-pbc-graded-finiteness-cohomology: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Cohomology of a finite type graded module over f^*B~ is a finite B-module. It does not state this combined proper-field preparation. Shared source tags: 01XZ, 01T6.

lem-trf-proper-field-invertible-coherent vs pqf-def-locnoeth: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Locally Noetherian schemes. It does not state this combined proper-field preparation. Shared source tags: 01T6.

lem-trf-proper-field-invertible-coherent vs pqf-lem-coherent-ft-locnoeth: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Coherence on locally Noetherian schemes. It does not state this combined proper-field preparation. Shared source tags: 01XZ.

lem-trf-proper-field-invertible-coherent vs pqf-lem-locnoeth-lft: The new node prepares a proper scheme over a field and concludes both Noetherianity and coherence of arbitrary invertible modules and the structure sheaf; the existing node states Finite type over a locally Noetherian base. It does not state this combined proper-field preparation. Shared source tags: 01T6.

lem-trf-curve-pullback-tensor-euler vs def-sc-tensor-power-open-restriction-comparisons: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Canonical restriction tensor, tensor-power and numerator comparisons. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs def-sc-tensor-pullback-power-comparison: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Canonical tensor-pullback, tensor-product and tensor-power comparisons. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs def-sfb-pencil-orbit-bundle-norm: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Orbit tensor bundle and norm section for a finite family of automorphisms. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs def-sfb-tensor-power-pullback-comparisons: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Tensor powers of module isomorphisms, with the canonical pullback power comparisons. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-pc-adjoint-module-pullback-monoidal: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states The adjoint scheme-module pullback is strong monoidal. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-pc-degree-base-change: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Degree: base change and tensor products. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 0AYV.

lem-trf-curve-pullback-tensor-euler vs lem-pc-module-pinned-tensor-stalk-square: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Canonical module tensor pullback square on stalks. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-pc-module-pullback-tensor-coherence: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Coherence of the recorded module pullback tensor comparison. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-pc-open-localized-tensor-homology: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Open restriction of ordinary tensor homology. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-pc-open-localized-tensor-natural: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Natural sheaf tensor comparison on a localized open site. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-pc-open-restriction-tensor-natural: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Naturality of canonical open restriction tensor comparison. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-pc-open-restriction-total-tensor: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Canonical open restriction commutes with total tensor complexes. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-pc-scheme-pullback-monoidal-existing: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states The existing scheme-module pullback functor is strong monoidal. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-ample-pullback-ideal-affine-section: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Ideal-supported affine sections in powers of an ample pullback. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-boundary-coefficient-degree-split: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Splitting off the first coefficient block before pullback. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-boundary-coefficient-tensor-product: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states The coefficient-degree comparison respects the ideal tensor pairing. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-boundary-pullback-tensor-braiding: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Symmetry of the fixed boundary tensor pullback comparison. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-boundary-pullback-tensor-unit: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Normalization of the canonical boundary pullback tensor comparison. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-external-open-coefficient-normalized: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Normalized coefficient-sheaf isomorphism for open base change. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-external-sections-components: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Explicit external section components and their naturality. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-external-sections-open-comparison: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Identification of an explicit external section component on an open subscheme. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-invertible-tensor-power-block-interchange: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Canonical concatenation of invertible tensor powers commutes with block interchange. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-localized-open-kflat-tensor-restriction: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states K-flat tensor models on the localized open site. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-localized-open-sheafification: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Sheafification commutes with localized open-site transport. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-localized-open-tensor-equivalence: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Natural tensor comparison for the localized open-site equivalence. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-picard-external-coefficients-affine-cech-differential: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states PicardExternalCoefficientsAffineCechDifferential. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-picard-external-right-rectangle-symmetry: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Natural symmetry of external coefficient section functors. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-pullback-monoidal-unit-comparison: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Monoidal pullback counit equals the canonical structure-sheaf comparison. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-pullback-tensor-power-iso: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Usual module pullback commutes with tensor powers. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-scalar-cup-coefficient-naturality: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Scalar cup product naturality in coefficients. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-scalar-cup-pullback-naturality: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Scalar cup product naturality under pullback. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-scalar-open-tensor-transport: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Scalar-linear tensor-section transport along an open immersion. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-scalar-pullback-tensor-coefficient: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Scalar pullback and tensor coefficient square. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-tensor-ideal-section-coefficient-comparison: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Coefficient coordinates for raw homogeneous ideal multiplication. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-tensor-power-open-restriction-addition: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Tensor-power addition comparison under open restriction. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-tensor-power-section-open-restriction: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Tensor-power section equations and transitions under open restriction. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-tensor-power-section-open-restriction-N: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Canonical tensor-power restriction comparison preserves section powers. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-tensor-power-section-open-restriction-T: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Canonical restriction numerator comparison intertwines transition sheaf morphisms. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-sc-tensor-pullback-power-append: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Tensor pullback preserves appending one tensor factor. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-trf-curve-euler-tensor-generic-rank: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Euler characteristic of an invertible twist on an integral proper curve. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 0AYV.

lem-trf-curve-pullback-tensor-euler vs lem-weil-pbc-base-change-tensor-distrib: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Base change distributes over tensor products of modules. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-weil-pbc-finite-structure-tensor-comparison-composition: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Tensor coherence of the pinned pullback composition comparison. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-weil-pbc-ideal-power-product-restriction-zero: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Restriction preserves vanishing of ideal-power products. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-weil-pbc-invertible-pullback-tensor: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Pullback and tensor product of invertible modules, and their fibres. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD, 01CT.

lem-trf-curve-pullback-tensor-euler vs lem-weil-pbc-module-pullback-tensor: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Pullback of modules commutes with tensor products, compatibly with sections. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-weil-pbc-module-pullback-tensor-iso-criterion: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states A section-compatible tensor-pullback comparison is an isomorphism. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-weil-pbc-module-restriction-tensor-comparison: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Restriction of a sheaf tensor product to an open immersion. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD.

lem-trf-curve-pullback-tensor-euler vs lem-weil-pbc-tensor-power-section-nonvanishing-pullback: The new node gives the Euler increment on an integral proper curve after arbitrary scheme pullback, including the tensor comparison and rank-one specialization; the existing node states Tensor-power sections pull back with inverse-image nonvanishing locus. The existing statement does not give that pullback Euler increment with these hypotheses. Shared source tags: 01CD, 01CT.

lem-trf-proper-field-invertible-coherent vs pqf-lem-coherent-ft-locnoeth: that node assumes a locally Noetherian scheme and gives coherence iff quasi-coherent finite type; it does not provide the Noetherian proper-field preparation. The extracted task must construct that hypothesis as in returned Step 1.

lem-trf-curve-pullback-tensor-euler vs lem-trf-curve-euler-tensor-generic-rank: that node takes an invertible module and an arbitrary coherent module already on C and retains their generic rank r. It states no pullback tensor identification. The extracted task establishes the generic rank-one specialization and comparison for modules originally on an arbitrary X.

lem-trf-curve-pullback-tensor-euler vs lem-pc-degree-base-change: the latter's tensor clause assumes an effective-divisor second factor, while this task uses any two invertible modules and any morphism from an integral proper curve.

## Unfinished work

The two new nodes intentionally remain statement-only unsplit tasks, as the return requires. No Lean was written and no compiler or build was run.
