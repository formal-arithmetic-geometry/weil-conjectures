## Worker report

Files written:

- dag/nodes/sec-trace-formula/lem-trf-scheme-zariski-etale-quasi-coherent-equivalence.json: repaired parent; statement unchanged; four assembly steps.
- dag/nodes/sec-trace-formula/lem-trf-etale-extension-free-presentations-hom.json: statement, unsplit; no Mathlib match after LeanFinder, LeanSearch, Loogle and grep plus a second semantic phrasing.
- dag/nodes/sec-trace-formula/lem-trf-etale-presented-module-effective-recovery.json: statement, unsplit; no Mathlib match after LeanFinder, LeanSearch, Loogle and grep plus a second semantic phrasing.
- dag/nodes/sec-trace-formula/lem-trf-zariski-etale-functor-comparison-square.json: statement, unsplit; no Mathlib match after LeanFinder, LeanSearch, Loogle and grep plus a second semantic phrasing.

Attachments: none. No project declaration under WeilConjectures carries the exact item tag or the complete statement. The recorded Sheaf theorem has a sorry at line 347 (and helper sorries at 70, 218, 232), so is not an attachment.

WANTED: none.

The returned defect was proof granularity, not the mathematical statement. The sandbox initially contained only the dispatcher .brief markers; there was no report, node or search log to reuse. I copied the current repository item as the repair baseline, retaining its statement, citations, searches, ancestry and maintainer metadata. The original ten-step proof is reproduced verbatim below as work briefs. Nothing was silently discarded, and no Lean, compiler, Lake or repository git command was used.

Nothing remains unfinished in this split. The three new nodes intentionally remain statement-only, with empty proof/proof_deps and null proof_origin for other workers.

## Repair of the return

The old work is assigned as follows:

- lem-trf-etale-extension-free-presentations-hom: original steps 1, 2, 3, 4; 2503 characters of argument.
- lem-trf-etale-presented-module-effective-recovery: original steps 5, 6, 7; 2190 characters of argument.
- lem-trf-zariski-etale-functor-comparison-square: original steps 8, 10; 2198 characters of argument.
- Parent: original step 9, the rank-one descent argument, and the short assembly. Parent proof length is 2306 characters, below 3000.

The three tasks separate actual arguments of comparable size. The first must construct free presentations and prove the Hom and restriction interfaces, not an equivalence; the second must lift the presentation arrows, establish a triple-overlap cocycle and effectivity, and glue the local maps, not assert all functorial comparisons; the third proves the mixed ringed-site square and flat-base-change section maps, with no line-module result or quasi-coherent essential surjectivity. No new node restates the entire item. This is the expressly requested re-split of an existing long proof, not an attempt to replace its proof by relabelling one lemma.

## Review by Q106

I read descent.tex at remark-change-topologies-ringed-sites (03FH), lemma-quasi-coherent-gives-quasi-coherent (03DV), lemma-fully-faithful-associated (0GN7), proposition-equivalence-quasi-coherent (03DX), lemma-equivalence-quasi-coherent-properties (05VG), and proposition-equivalence-quasi-coherent-functorial (03LC), together with proposition-fpqc-descent-quasi-coherent (023T), lemma-finite-locally-free-descends and coherent.tex lemma-flat-base-change-cohomology (02KH). The item agrees with the small-etale cases, keeping its separated hypothesis (a valid restriction of the source's quasi-separated hypothesis). The forward functor is tensor pullback, not the untensored abelian inverse image. The inverse and normalization refer to open-section restriction, not arbitrary etale objects. The source proof deliberately omits the cocycle check; original step 6 supplies it, and the effective-recovery node explicitly requires it.

For the first new statement, I checked that the tensor-sections formula comes from the existing arbitrary-module comparison, whereas the unsheafified section formula is asserted only for quasi-coherent inputs. Free presentations use arbitrary small index sets and no finite generation. Restriction compatibility is required only for etale maps in this task. The unit is the identity under the canonical open-section identification, and its Hom consequence is only asserted for quasi-coherent modules. These are exactly old steps 1-4, not a claim of essential surjectivity.

For the second new statement, the scheme, module, cover, presentations and projection maps are introduced internally. The specified cokernels, their comparison maps and the triple-overlap cocycle are conclusions, not unspecified choices whose existence is assumed. I checked the direction of phi_ij against b_j inverse composed with b_i. The pullbacks to overlaps are quasi-coherent; the etale cover is fpqc as a family, without assuming every member is quasi-compact. The old local lifting, effectivity and sheaf gluing arguments remain assigned here, including the inverse local maps and the triangle-identity normalization of the counit. It does not assume the parent's equivalence.

For the third new statement, all four functors and rings are specified. The open-section direct-image square is valid for any etale module, and its left adjoint comparison is therefore available for every Zariski module. Only the direct-image/base-change clause assumes H quasi-coherent and a quasi-compact separated. Separated implies quasi-separated before 02KH is applied; the base-change map is flat because v is etale. The target of that base-change map lives on V, with U_V the correct fibre product. The natural section maps and their open normalization are retained, not replaced by an arbitrary existence of an isomorphism.

I read the statement of every citation in the repaired parent. Step 1 uses the first new node for quasi-coherent preservation, full faithfulness and the unit, and the second for quasi-coherent restriction and the counit; these yield inverse restricted adjunctions. Step 2 uses the first node for the structure sheaf, etale restriction and the Hom bijection; def-sc-invertible-module and def-trf-algebraic-space state precisely the two notions of line module used; lem-weil-pbc-fpqc-finer-than-etale supplies the covering hypothesis, and clause (2) of lem-pc-fpqc-descent explicitly preserves and reflects finite local freeness of the given rank r=1. The line-module presentation is an explicit elementary application of its trivialization. Step 3 takes the actual canonical pullback comparison from the third new statement; lem-weil-pbc-module-pullback-quasi-coherent supplies the quasi-coherence needed to use the first node's unsheafified tensor-sections identification. Step 4 takes ordinary direct-image quasi-coherence and the normalized sheaf isomorphism from the third node, then site quasi-coherence from the first. Invariance of a local-presentation predicate under isomorphism is elementary. No cited proof, definition-only node, or unnamed source lemma is substituted for its statement. citations.json copies the cited statements verbatim.

For small cases I checked the empty scheme and empty covering (only possible for the empty base), the zero module and empty free index sets, the identity morphism, an open immersion, and Spec A with an arbitrary, possibly infinitely generated A-module. Recovery does not assume affine intersections or a separated base. For the functor square the identity/open cases give identity section maps; a nonflat scheme map still allows the pullback comparison, but the pushforward comparison only uses flat etale tests, and it is not promoted to arbitrary nonflat base change. Rank one descends as a specified constant rank, so no inference from merely finite local freeness of unspecified rank is used.

I searched the entire DAG by tags 03DV, 0GN7, 03DX, 03LC, 070S and by concepts; blueprint_refs.py searches included quasi-coherent, fully faithful, 03DX, 03LC and etale module, and ancestor returned lem-trf-local-term-locality. I read all same-tag candidate statements and the closely related scheme line-module and kernel statements. The inherited historical ancestry through the section-algebra/ampleness specialization chain is kept, with each new node's via beginning at this item. No chapter/unit route is changed. The two surviving off-unit proof tools, fpqc refinement and descent, and the pullback quasi-coherence lemma are generic module tools already used by the old proof and are declared in split_report.tool_uses, not newly approved top-level tool_uses.

All fifteen new searches actually ran with msearch.py; raw outputs are copied into mathlib_searches and retained in the sandbox. I read their hits and the candidate Mathlib files AlgebraicGeometry/Modules/Sheaf.lean, Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean, Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean, and Algebra/Category/ModuleCat/Descent.lean. The hits supply general adjunctions, local-presentation data, or affine extension-of-scalars comonadicity. They do not supply the mixed topology comparisons, the global scheme recovery, or the full first task in one line. In particular, Presentation.map is only the presentation-mapping subargument; it does not identify the topology change or prove the unit/Hom assertion. No new node is a Mathlib leaf.

## Not duplicates

- lem-trf-etale-extension-free-presentations-hom vs lem-trf-scheme-zariski-etale-quasi-coherent-equivalence: the existing parent asserts equivalence, rank-one correspondence and both functorialities together; this is one balanced internal work package of its returned long proof, without the other packages.
- lem-trf-etale-extension-free-presentations-hom vs lem-trf-zariski-etale-tensor-sections: the existing node gives the arbitrary-module sheafified tensor-sections formula and restriction functor, but neither quasi-coherent free-presentation/Hom recovery nor the mixed morphism/base-change square.
- lem-trf-etale-extension-free-presentations-hom vs def-trf-space-module-scheme-restriction: the existing node defines restriction to opens and its scalar comparison, not a theorem of quasi-coherent preservation, effectivity or canonical comparison isomorphisms.
- lem-trf-etale-extension-free-presentations-hom vs lem-sc-etale-tensor-sections-right-exact: the existing node proves cokernel preservation for the sheafified ULift tensor-section functor; it supplies neither site quasi-coherent local free presentations and the unit/Hom theorem, nor the mixed morphism comparison square.
- lem-trf-etale-presented-module-effective-recovery vs lem-trf-scheme-zariski-etale-quasi-coherent-equivalence: the existing parent asserts equivalence, rank-one correspondence and both functorialities together; this is one balanced internal work package of its returned long proof, without the other packages.
- lem-trf-etale-presented-module-effective-recovery vs lem-trf-scheme-etale-invertible-comparison: the existing node concerns only rank-one modules and etale restriction; it does not give arbitrary quasi-coherent presentations/recovery or arbitrary scheme-map pullback/direct-image comparisons.
- lem-trf-etale-presented-module-effective-recovery vs def-trf-space-module-scheme-restriction: the existing node defines restriction to opens and its scalar comparison, not a theorem of quasi-coherent preservation, effectivity or canonical comparison isomorphisms.
- lem-trf-zariski-etale-functor-comparison-square vs lem-trf-scheme-zariski-etale-quasi-coherent-equivalence: the existing parent asserts equivalence, rank-one correspondence and both functorialities together; this is one balanced internal work package of its returned long proof, without the other packages.
- lem-trf-zariski-etale-functor-comparison-square vs lem-trf-scheme-etale-invertible-comparison: the existing node concerns only rank-one modules and etale restriction; it does not give arbitrary quasi-coherent presentations/recovery or arbitrary scheme-map pullback/direct-image comparisons.
- lem-trf-zariski-etale-functor-comparison-square vs lem-trf-zariski-etale-tensor-sections: the existing node gives the arbitrary-module sheafified tensor-sections formula and restriction functor, but neither quasi-coherent free-presentation/Hom recovery nor the mixed morphism/base-change square.
- lem-trf-zariski-etale-functor-comparison-square vs def-trf-space-module-scheme-restriction: the existing node defines restriction to opens and its scalar comparison, not a theorem of quasi-coherent preservation, effectivity or canonical comparison isomorphisms.
- lem-trf-zariski-etale-functor-comparison-square vs lem-sc-etale-tensor-sections-right-exact: the existing node proves cokernel preservation for the sheafified ULift tensor-section functor; it supplies neither site quasi-coherent local free presentations and the unit/Hom theorem, nor the mixed morphism comparison square.

## Preserved argument briefs for the new workers

The following original proof text is retained verbatim; it is not placed in the statement-only nodes as a premature proof. Its cited existing dependencies have also been read against their statements.

### lem-trf-etale-extension-free-presentations-hom

Original step 1:

Write $L_T=\epsilon_T^*$ and $R_T=\epsilon_{T,*}$. By [lem-trf-zariski-etale-tensor-sections], $R_T$ is restriction to open subschemes and $L_TM$ is the sheafification of tensor sections, naturally in arbitrary $M$. For quasi-coherent $F$, [lem-sc-etale-qcoherent-descent] says that this presheaf already is a sheaf; hence $L_TF=F_{\mathrm{et}}$, with precisely the specified maps. The tensor formula gives $L_T\mathcal O_T=\mathcal O_{T,\mathrm{et}}$: the scalar multiplication map has inverse $r\mapsto r\otimes1$. By [lem-weil-pbc-ringed-topoi-module-adjunction], $L_T\dashv R_T$. Consequently $L_T$ preserves coproducts and cokernels: maps out of $L_T\operatorname{colim} M_i$ are, by adjunction, compatible families of maps $M_i\to R_TG$, equivalently compatible families $L_TM_i\to G$.

Cited nodes: lem-trf-zariski-etale-tensor-sections, lem-sc-etale-qcoherent-descent, lem-weil-pbc-ringed-topoi-module-adjunction.

Source: literature/stacks-project/descent.tex, 070S(2), lemma-compare-sites; 03FH(1), remark-change-topologies-ringed-sites; proof of 03DV, lemma-quasi-coherent-gives-quasi-coherent.

Original step 2:

For an etale $u:V\to T$ and quasi-coherent $F$, the restriction of $L_TF$ to $V_{\mathrm{et}}$ is $L_V(u^*F)$. Indeed at $v:W\to V$ the two values are $\Gamma(W,(u\circ v)^*F)$ and $\Gamma(W,v^*u^*F)$; [lem-pc-module-pullback-identity-composition] identifies these and their restriction maps. The module $u^*F$ is quasi-coherent by [lem-weil-pbc-module-pullback-quasi-coherent]. This also applies to open immersions.

Cited nodes: lem-pc-module-pullback-identity-composition, lem-weil-pbc-module-pullback-quasi-coherent.

Source: literature/stacks-project/descent.tex, 03FH(2), remark-change-topologies-ringed-sites, restricted to etale maps.

Original step 3:

Choose an affine open cover of $T$. On $V=\operatorname{Spec}A$, write $F|_V=\widetilde M$ by [lem-weil-pbc-affine-tilde-gamma-adjunction]. Choose a free-module presentation $A^{(I)}\to A^{(J)}\to M\to0$: take generators indexed by the elements of $M$ and relations indexed by the kernel of the resulting free surjection. The same affine tilde adjunction preserves all small colimits, so it gives $\mathcal O_V^{(I)}\to\mathcal O_V^{(J)}\to F|_V\to0$; $\widetilde A=\mathcal O_V$ by the localization description [lem-weil-pbc-spec-module-tilde-sections]. Apply the colimit-preserving $L_V$ of step 1 and the restriction identification of step 2. This supplies a free presentation of $L_TF$ on each $V_{\mathrm{et}}$, exactly the site quasi-coherence predicate [def-trf-space-quasi-coherent-module]. Thus $L_T$ takes quasi-coherent Zariski modules to quasi-coherent etale modules.

Cited nodes: lem-weil-pbc-affine-tilde-gamma-adjunction, lem-weil-pbc-spec-module-tilde-sections, def-trf-space-quasi-coherent-module.

Source: literature/stacks-project/descent.tex, 03DV, lemma-quasi-coherent-gives-quasi-coherent, proof of part (2).

Original step 4:

For every open $W\subseteq T$, $(R_TL_TF)(W)=\Gamma(W,F|_W)=F(W)$. These identifications respect restrictions and identify the adjunction unit with the identity. For quasi-coherent $F,H$ the adjunction therefore reads $\operatorname{Hom}(L_TF,L_TH)=\operatorname{Hom}(F,R_TL_TH)=\operatorname{Hom}(F,H)$. This proves full faithfulness, also with $T$ replaced by any scheme appearing in the following descent argument.

Cited nodes: lem-trf-zariski-etale-tensor-sections, lem-weil-pbc-ringed-topoi-module-adjunction.

Source: literature/stacks-project/descent.tex, 0GN7, lemma-fully-faithful-associated, proof.

### lem-trf-etale-presented-module-effective-recovery

Original step 5:

Let $G$ be a quasi-coherent module on $T_{\mathrm{et}}$. By [def-trf-space-quasi-coherent-module], choose a jointly surjective etale family $u_i:V_i\to T$ with a presentation $\mathcal O^{(I_i)}\to\mathcal O^{(J_i)}\to G|_{V_i}\to0$. The Zariski modules $K_i=\mathcal O_{V_i}^{(I_i)}$ and $P_i=\mathcal O_{V_i}^{(J_i)}$ are quasi-coherent by [lem-weil-pbc-quasi-coherent-module-coproduct-closure]. Step 1 identifies their images with the two displayed free etale modules; full faithfulness in step 4 lifts the presentation arrow uniquely to $h_i:K_i\to P_i$. Put $F_i=\operatorname{Coker}(h_i)$, quasi-coherent by [lem-weil-pbc-quasi-coherent-module-cokernel-image]. Preservation of cokernels in step 1 gives an isomorphism $b_i:L_{V_i}F_i\simeq G|_{V_i}$.

Cited nodes: def-trf-space-quasi-coherent-module, lem-weil-pbc-quasi-coherent-module-coproduct-closure, lem-weil-pbc-quasi-coherent-module-cokernel-image.

Source: literature/stacks-project/descent.tex, 03DX, proposition-equivalence-quasi-coherent, local presentation paragraph.

Original step 6:

On $V_{ij}=V_i\times_TV_j$, step 2 and the $b_i$ identify $L_{V_{ij}}(p_i^*F_i)$ and $L_{V_{ij}}(p_j^*F_j)$ with the same restriction of $G$. Full faithfulness in step 4 lifts $b_j^{-1}b_i$ uniquely to an isomorphism $\phi_{ij}:p_i^*F_i\to p_j^*F_j$. On triple products its images satisfy $(b_k^{-1}b_j)(b_j^{-1}b_i)=b_k^{-1}b_i$; faithfulness gives the cocycle equation for $\phi_{ij}$, including repeated indices. By [lem-weil-pbc-fpqc-finer-than-etale] this etale covering is fpqc. Apply clause (1) of [lem-pc-fpqc-descent] to obtain a quasi-coherent $F$ on $T$ and compatible isomorphisms $u_i^*F\simeq F_i$.

Cited nodes: lem-weil-pbc-fpqc-finer-than-etale, lem-pc-fpqc-descent.

Source: literature/stacks-project/descent.tex, 03DX, proposition-equivalence-quasi-coherent, overlap and effectivity paragraphs; 023T, proposition-fpqc-descent-quasi-coherent.

Original step 7:

The resulting maps $L_TF|_{V_i}\simeq G|_{V_i}$ agree on pairwise overlaps. They glue to an isomorphism $b:L_TF\simeq G$: for an etale object $W\to T$, restrict a section to the cover $W\times_TV_i\to W$, apply these local maps, and take the unique glued section of $G$. The inverse local maps give the inverse construction. Uniqueness in the sheaf equalizer [lem-weil-pbc-site-sheaf-sets-limits-sectionwise] proves compatibility with restriction and module operations. Hence $L_T$ is essentially surjective. Restricting $b$ to opens identifies $R_TG$ with $F$, so $R_T$ is its quasi-coherent inverse. The unit was the identity on open sections in step 4; the triangle identity says $R_T(\mathrm{counit}_G)$ is its inverse and therefore also the identity under these identifications. This proves the claimed normalization.

Cited nodes: lem-weil-pbc-site-sheaf-sets-limits-sectionwise.

Source: literature/stacks-project/descent.tex, 03DX, proposition-equivalence-quasi-coherent, final gluing paragraph; 0GN7, lemma-fully-faithful-associated, restriction inverse.

### lem-trf-zariski-etale-functor-comparison-square

Original step 8:

For any scheme morphism $a:U\to T$ and any etale module $G$ on $U$, the two direct images $R_Ta_{\mathrm{et},*}G$ and $a_*R_UG$ agree: at an open $W\subseteq T$ both are $G(a^{-1}W\hookrightarrow U)$ with the same ring action. The evaluation formula for small etale direct image is [lem-trf-space-etale-module-pushforward-restriction]. Using the two ringed-topos adjunctions [lem-weil-pbc-ringed-topoi-module-adjunction] and scheme adjunction [lem-pc-module-pullback-adjunction], one obtains
$$\operatorname{Hom}(a_{\mathrm{et}}^*L_TF,G)=\operatorname{Hom}(F,R_Ta_{\mathrm{et},*}G)=\operatorname{Hom}(a^*F,R_UG)=\operatorname{Hom}(L_Ua^*F,G).$$
The natural representing-object comparison is therefore an isomorphism. This is the canonical comparison, because all three bijections use the specified units and counits. By [lem-weil-pbc-module-pullback-quasi-coherent], $a^*F$ is quasi-coherent, so step 1 identifies its left side with the specified tensor-sections sheaf. This proves $(a^*F)_{\mathrm{et}}\simeq a_{\mathrm{et}}^*F_{\mathrm{et}}$ naturally for arbitrary $a$.

Cited nodes: lem-trf-space-etale-module-pushforward-restriction, lem-weil-pbc-ringed-topoi-module-adjunction, lem-pc-module-pullback-adjunction, lem-weil-pbc-module-pullback-quasi-coherent.

Source: literature/stacks-project/descent.tex, 03FH(2), remark-change-topologies-ringed-sites; 03LC(1), proposition-equivalence-quasi-coherent-functorial.

Original step 10:

Finally let $a:U\to T$ be quasi-compact and separated in the statement's sense. By [lem-trf-space-qc-separated-etale-local] these agree with the ordinary scheme properties; [lem-pc-separated-quasi-separated] gives quasi-separatedness. Thus $a_*H$ is quasi-coherent by [pqf-lem-pushforward-qcoh]. For any etale $v:V\to T$, form $U_V=U\times_TV$, with maps $a_V:U_V\to V$ and $v':U_V\to U$. Since $v$ is flat [def-weil-etale-morphism], degree zero of [lem-pc-flat-base-change-cohom] gives the canonical isomorphism $v^*a_*H\simeq a_{V,*}v'^*H$. Taking sections over $V$ identifies $(a_*H)_{\mathrm{et}}(V)$ with $\Gamma(U_V,v'^*H)$, which is $(a_{\mathrm{et},*}H_{\mathrm{et}})(V)$ by [lem-trf-space-etale-module-pushforward-restriction]. These are the canonical base-change maps, hence are natural in $V$ and $H$ and give the required sheaf isomorphism. Its source is site quasi-coherent by step 3, so the target is too. On an open $V=W\subseteq T$, base change is restriction to $a^{-1}W$ and the displayed section comparison is the identity of $\Gamma(a^{-1}W,H)$. This proves also the required normalization of direct image.

Cited nodes: lem-trf-space-qc-separated-etale-local, lem-pc-separated-quasi-separated, pqf-lem-pushforward-qcoh, def-weil-etale-morphism, lem-pc-flat-base-change-cohom, lem-trf-space-etale-module-pushforward-restriction.

Source: literature/stacks-project/descent.tex, 03LC(3), proposition-equivalence-quasi-coherent-functorial, proof; 02KH, coherent.tex lemma-flat-base-change-cohomology, degree 0.

### Parent rank-one argument (original step 9)

If $F$ is Zariski locally free of rank one [def-sc-invertible-module], steps 1 and 2 send each trivialization to a trivialization of $L_TF$ by $\mathcal O_{T,\mathrm{et}}$, so it is a line module [def-trf-algebraic-space]. Conversely a line module is site quasi-coherent (use the free presentation $0\to\mathcal O\to G\to0$ on a trivializing etale cover). By steps 5--7 write it as $L_TF$. On that cover, step 2 and full faithfulness give $u_i^*F\simeq\mathcal O_{V_i}$. The cover is fpqc by [lem-weil-pbc-fpqc-finer-than-etale]; clause (2) of [lem-pc-fpqc-descent], with rank $r=1$, makes $F$ Zariski locally free of rank one. Since the categories of line modules are full subcategories, the established equivalence restricts to the claimed equivalence of invertible modules.
