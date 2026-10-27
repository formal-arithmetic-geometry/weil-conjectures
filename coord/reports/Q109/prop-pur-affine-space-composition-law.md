# Worker report

1. Files written: the item dag/nodes/sec-smooth-purity/prop-pur-affine-space-composition-law.json is split with its statement unchanged. Three new statement-only nodes (kind statement, status unsplit, Mathlib verdict no match) are:
- dag/nodes/sec-smooth-purity/lem-pur-ordered-adjoint-tower-regrouping.json
- dag/nodes/sec-smooth-purity/lem-pur-even-line-product-integration-symmetry.json
- dag/nodes/sec-smooth-purity/lem-pur-ordered-affine-transpose-projection.json

2. Attachments: none. The project declaration AlgebraicGeometry.ProEtale.AffineSpacePurity.affineSpacePurityComposition in lean/Sheaf/Paper/AffineSpacePurityComposition.lean ends with sorry. Project-wide searches of lean/WeilConjectures by the blueprint tag and by ordered tower/trace/projection concepts found no exact closed declaration. Generic projection transposes are not this theorem.

3. WANTED: none.

4. The returned proof was 11979 characters and ten steps. The sole return asks to distribute the work, preserve the item statement, add at least three comparable statement-only obligations, and keep the assembly at most 3000 characters. This delivery adds three independent arguments and its assembly has 2353 characters. The returned source fields pointed to the older blueprint; the replacement proof sources point to main-20261015/sk-prop-sp-composition. The two versions' four proof paragraphs have the same route. There is no blueprint_update on the item. The actual statement, stmt_deps, Lean and audit records are retained. The sandbox initially contained only dispatcher markers: no retained split, searches or report existed. I copied the current returned repository item, and attempted the required initial dry run before creating the split; it could not validate an absent report. Work now continues from that copy, without touching the shared repository.

5. All requested stage-1 work is present; the three arguments are deliberately unsplit for future workers. No Lean file was edited and no compiler, Lake or build tool was run.

## Argument allocation

The three new nodes have genuinely different mathematical objects. The first is a theorem for arbitrary finite strings of categories, adjoint functors, coherent compositors and natural transformations. It contains no schemes or affine permutations. The second identifies arbitrary-coefficient transposes of the actual affine tower, and the pasted-counit equation; it asserts no regrouping or permutation invariance. The third concerns only concrete compact-support relative products, recursively specified maps to the tensor unit, finite-Tor domains and even Tate factors; it assumes no exceptional adjoint. None is the original two-clause statement under another name.

- Old Step 1: geometry and adjunction domains remain in assembly Step 1 and the explicit finite coefficient/ctf hypotheses of the two geometric new nodes. Its reflection argument is already the statement of det-pe-finite-tor-comparison-noetherian (and the more general lem-sf-bounded-below-ctf-reflection); reuse it, rather than create a duplicate. No comparison on an unbounded tensor is invoked.
- Old Step 2: the ramified-stage tensor calculation and pullback compatibility are already clauses of lem-pur-vector-integration-site-comparison, whose statement supplies the actual normalized trace and transpose comparisons. Assembly Step 1 cites that existing node; the new geometric nodes retain arbitrary n. No new node is appropriate for the elementary tensor reassociation.
- Old Steps 3 and 4: lem-pur-ordered-adjoint-tower-regrouping carries the coherence of the mate compositor, its units, naturality and the induction for every cut in an ordered string. Its proof task includes the original substitution/naturality induction; the detailed old argument is retained below. The application to the two coordinate blocks remains assembly Step 2.
- Old Step 5: actual line-trace base change is explicitly asserted by lem-amb-affine-space-top-trace at d=1, with comparison of the actual ordinary/pro-etale traces by lem-pur-vector-integration-site-comparison. Assembly Step 3 checks its hypotheses. The old compactification calculation is retained below as the explanation of this existing source result, not silently removed.
- Old Step 6: lem-pur-ordered-affine-transpose-projection carries the exact pasted-counit identity and the induction extracting K by the projection formula. Its statement fixes the actual inverse projection with both symmetries, so an arbitrary map of the same type cannot satisfy the obligation by fiat.
- Old Steps 7 and 8: assembly Step 3 retains the one-dimensional object isomorphism and invokes the existing lem-pur-affine-space-product-domain. This old induction was already a separate node and is not copied. It verifies the M and V_m base coefficients before each inverse projection map.
- Old Step 9: assembly Step 4 invokes the existing binary actual-trace factorization. The tensor-power induction and the coherence of the specified products belong to lem-pur-even-line-product-integration-symmetry.
- Old Step 10: lem-pur-even-line-product-integration-symmetry carries the tensor-unit naturality, adjacent-transposition argument, rank-one local-generator identification, signs for line and block interchanges, and compatibility with the coefficient-first inverse projection. Assembly Step 5 retains the final use of the injective exceptional Hom bijection.

Every old argument is reproduced verbatim below, with its new obligation identified above; none is abbreviated away. The proof sketches are in this report only, not in the statements of unsplit nodes.

## Not duplicates

- lem-pur-ordered-adjoint-tower-regrouping vs lem-weil-pbc-mate-pasting: the latter is a two-square mate-pasting identity; the new node includes extension of arbitrary adjacent natural transformations through a finite ordered string and the all-cuts induction.
- lem-pur-ordered-adjoint-tower-regrouping vs lem-trf-adjoint-composition-coherence: the existing statement transfers a triple's associativity between adjoint compositors; it has neither the separate F functors nor the ordered natural-transformation extension.
- lem-pur-ordered-adjoint-tower-regrouping vs def-pur-affine-space-comparison: the latter defines a geometric recursion and its specified comparators, not the general all-cuts theorem for arbitrary categories and natural transformations.
- lem-pur-ordered-affine-transpose-projection vs lem-pur-affine-space-trace-factorization: the existing statement is the binary recurrence at the unit coefficient, conditional on base change and finite-Tor output; the new statement is the coefficient-extraction identity for every K and the actual composite-adjunction transpose formula.
- lem-pur-ordered-affine-transpose-projection vs lem-pur-system-tensor-transpose-composition: the latter is about strict coefficient systems, dualizing objects and co-smooth tensor maps; the new statement uses finite-stage ordered affine-line comparisons and their actual specified line integrations.
- lem-pur-ordered-affine-transpose-projection vs lem-pur-projection-purity-agreement: the latter compares a diagonal/DNC orientation with the ordered affine route; this new node makes no diagonal or smooth-purity comparison.
- lem-pur-even-line-product-integration-symmetry vs lem-sf-kunneth-coherence: the existing theorem assumes a six-functor datum. The new statement is for the concrete finite operations, verifies their required coherence on the stated domains, and concludes equality of specified integrations and coefficient transposes.
- lem-pur-even-line-product-integration-symmetry vs lem-pur-finite-forward-product-symmetry: the latter is a two-factor forward-map equation and assumes no inverses; the new statement concerns inverse iterated products, recursion into the unit, all coordinate permutations and the even Tate identification.
- lem-pur-even-line-product-integration-symmetry vs lem-amb-linear-trace-invariance: the latter concerns the normalized ordinary-etale coordinate-tower counit under GL_d; the new node concerns recursively given maps through concrete pro-etale relative products and the coefficient projection formula. It does not assume identification with a higher-dimensional counit.
- lem-pur-even-line-product-integration-symmetry vs prop-pur-affine-space-composition-law: no exceptional functor or comparison is input to the new node, and no block-composition equality is its conclusion. It is the tensor-integration argument used to prove coordinate invariance of those comparisons.

## Searches read

Before creating nodes I searched all dag/nodes by the actual statement concepts (Tor reflection, ordered regrouping, iterated transpose/projection, integration/permutation), and used tools/blueprint_refs.py searches for finite Tor reflection, ordered comparison regrouping, affine line trace, transpose projection formula, integration permutation; the separate-word searches ordered tower, transpose projection, Tor comparison and affine composition were also run. I read the relevant matches: ordered comparison definition, top trace, vector integration comparison, binary trace factorization, product-domain induction, strict-system transpose theorem, smooth composition factors, trace-basic and linear trace invariance. The latter smooth-purity consequences are not substituted for this earlier affine-line route. No match states any of the three new obligations. All three blueprint.same_as lists are empty; their from.node is the imported item, with exact proof paragraph and returned-step locations, via=[].

Mathlib searches were run only by msearch.py and are logged in searches.jsonl. Each new node records its own semantic query, distinct second wording in LeanSearch, a Loogle query and source grep, exactly as run. All four services returned answers. Generic mateEquiv_hcomp/vcomp and conjugateEquiv_id (Mates.lean:170,209,319), comp_counit_app (Basic.lean:580), and leftAdjointCompNatTrans_assoc (CompositionIso.lean:157) were inspected: they do not assert the ordered natural-transformation extension, nor a finite-coefficient compact-support tower or trace. Thus no new node is a one-line Mathlib specialization. The analytic product-integral hits and linear-algebra trace-base-change hits are different notions. Broader preliminary domain/line searches are retained in the log but not invented as records for new nodes.

## Review by Q109

I read delivery-errors B--E in full, the current node and its ten steps, GOAL.md, the chapter and unit sk-prop-an (especially Step 6), and main-20261015's composition-law statement and all four proof paragraphs. The item statement remains byte-identical to the returned head; d,e>=1, finite A_{E,n}, separated finite-type Y, the ctf K domain, the reversed exceptional compositor, the canonical source identifications, sign and actual block-swap equality are all retained.

For the first new node I read Stacks categories.tex Tag 0DV0 (lemma-compose-counits), including the displayed counit formula and its Hom-bijection proof, and Tag 0B65 (lemma-transformation-between-functors-and-adjoints), including its counit square and proof. These give the normalization used in the new abstract statement; the ordered-string induction is an agent-written elaboration of blueprint Step 2, not a claim that either tag states the whole induction. I checked the indices: P_ij:C_j to C_i has right adjoint G_ij:C_i to C_j; F_jk Gamma_ij and Gamma_jk at G_ij K have the right source and target; c inverse then ends in G_ik K. r=0, r=1, endpoint cuts i=j or j=k and noninvertible eta all work. This is the preserved nontrivial induction, not a new axiom of the comparisons.

For the transpose node I read the current definitions of the line comparison and affine ordered comparison, including their exact two-symmetry Pi formula; the composite-adjunction statement; the binary trace factorization statement and proof's pasted counit; and the same Stacks 0DV0 normalization. The new assertion uses tau_f at F_g K, not at an untwisted K, and its source is Rg_! Rf_! F_f F_g K. At m=0 it is the unit, and at m=1 it is exactly the defining projection-then-trace. The arbitrary-K identity neither assumes purity isomorphy nor permutation invariance. Its projection-coherence task is for the actual finite operations. The old proof's abstract six-functor coherence reference cannot be treated as an unrestricted concrete hypothesis.

For the symmetry node I read the current product-domain statement and its factorwise inverse-map justification, the binary trace-factorization statement, lem-pur-finite-forward-product-symmetry, and all four clauses of lem-sf-kunneth-coherence. This exposed the abstract-datum boundary: that last theorem assumes a six-functor datum, while this finite comparison proof is supposed to establish compatibilities for the concrete operations. The extracted obligation now explicitly proves the needed concrete coherence on its stated finite-Tor domains and assumes no duality datum. It does not simply cite the abstract theorem without its hypotheses. Its J_m are recursive maps and no coordinate invariance is assumed; proving t tensor ... tensor t is fixed by the induced swaps is real work. I checked m=1, the first adjacent swap m=2, identity permutations, repeated swaps, empty Y, and coefficient characteristic two. I also checked that a rank-one generator b makes the unshifted flip send b tensor b to itself; the shifts are -2d and -2e, giving the sign +1 independently of K. Thus no claim about symmetry of two arbitrary unshifted coefficient sheaves is hidden.

Assembly citation check, statement by statement: Step 1 takes finite-Tor exceptional preservation from thm-sf-preservation-class(2), the actual bounded-below etale-origin Hom bijection from thm-sf-ambient-adjoint-class(2), the equivalence of the ctf categories from det-pe-finite-tor-comparison-noetherian, and the actual trace/projection/transpose and root-normalized twist equalities from lem-pur-vector-integration-site-comparison. Finite type over the field gives Noetherianity by the cited lem-weil-pbc-finite-type-over-noetherian; finite A is Noetherian and these bases are qcqs, so the equivalence's hypotheses hold. The compactifications and their finite dimension bounds are the standard projective ones specified in the comparison definition.

Step 2 specializes the new abstract all-cuts theorem, and its cited affine-space definition supplies the actual coherent alpha, c, twist and pullback recursion. thm-sf-ctf-stability is used only in clauses (i),(ii),(iv), not its duality assertions: P and F preserve the ctf categories, while Step 1 handles G. The defining line comparison is natural because both its projection map (lem-weil-finite-compact-projection-formula) and the Hom bijection are natural. The cut has the same orientation c inverse as the item display.

Step 3 uses lem-amb-affine-space-top-trace only for d=1, for both isomorphy and the equality for actual base-changed traces. Here N=ell^r>=1 kills A, ell is invertible, and every tower base is Noetherian; the comparison of the actual maps is Step 1's vector-integration comparison. The product-domain statement is applied to M=A(1)[2] with U isomorphic to A_Y; prop-weil-twist-preserves supplies local freeness of the unshifted Tate line. The derived shift adjusts its Tor interval and causes no failure of finiteness. The existing node supplies V_m ctf and the typed binary inverses; no higher-dimensional trace is substituted for I_m.

Step 4 takes exactly the new arbitrary-K transpose formula and exactly the existing binary recurrence. The latter asks that line integrations commute with base change over every allowed base: Step 3 checked that, not just one change of base. It also asks for finite-Tor V_m, supplied by the product-domain node. Step 5 takes the new conditional symmetric-integration conclusion with J_m=I_m, then uses the natural injective Hom bijection already cited in Step 1. It therefore proves equality of the actual comparisons, not merely parity of signs or equality of source objects.

B1--B7: each new node introduces its objects and hypotheses, is TeX text, has no proof steps/proof dependencies/proof sketch, has source and precise blueprint ancestry, and records four real Mathlib searches. C1/C4: every assembly fact has the matching cited statement, and citations.json copies the full verbatim statement for every uses pair, including reuse from earlier steps. D1/D2: the abstract ordered-category theorem, arbitrary-K transpose identity and tensor-product recursion have separate hypotheses and arguments; no single node restates the whole item. E: the explicit tests above include the small ranks, empty schemes and ramified coefficient stages. No statement dispute, source counterexample or route departure was needed. All assembly steps are below 2000 characters and their total is below 3000. The existing long argument has not been hidden inside an elementary step.

The return's one numbered requirement is repaired by the three nodes and short assembly; the complete retained argument follows so another worker can recover every argument without relying on a shortened paraphrase.

## Returned proof retained verbatim

### Returned Step 1

Fix the coefficient and geometric domains. All the projections in the coordinate towers are separated of finite type between separated finite-type $k$-schemes, with their standard projective compactifications. Their bases and sources are Noetherian by [lem-weil-pbc-finite-type-over-noetherian], applied to their finite-type structural maps to $\operatorname{Spec}k$: a field is Noetherian since its only ideals are $0$ and the unit ideal. The adjunction on bounded-below etale-origin inputs is [thm-sf-ambient-adjoint-class]; [thm-sf-preservation-class] implies that each intermediate exceptional pullback of $K$ is bounded constructible of finite Tor amplitude. Thus every occurrence of $\gamma_{p_d,Rp_e^!K}$ is in its declared domain. Twists are locally free rank-one coefficient sheaves by [prop-weil-twist-preserves]. We may calculate compact-support morphisms on the ordinary etale site: [lem-sf-proetale-constructible-origin] supplies etale representatives, [thm-weil-pbc-site-comparison] is fully faithful on $D^+$, [lem-sf-class-compact-support-comparison] identifies the two compact-support functors, and [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] applies to $\nu$ as well as to scheme pullbacks. The exceptional adjunction is transported by the actual Hom bijection of [thm-sf-ambient-adjoint-class], rather than by an unbounded pro-etale adjoint assumption. The finite Tor condition is reflected on an etale representative: tensor it with any etale module sheaf and apply the exact, fully faithful, monoidal $\nu^*$; the resulting tensor has the required cohomological vanishing, which is reflected on each cohomology sheaf by the faithful exact inverse image (faithfulness on sheaves follows from full faithfulness on complexes concentrated in degree zero). This reflection does not require applying bounded-below full faithfulness to an unbounded tensor complex. These facts identify the transposes and permit checking their equality on the etale site.

Uses: thm-sf-ambient-adjoint-class, thm-sf-preservation-class, prop-weil-twist-preserves, lem-sf-proetale-constructible-origin, thm-weil-pbc-site-comparison, lem-sf-class-compact-support-comparison, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-finite-type-over-noetherian

Source: {'document': 'literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-an/prop-pur-affine-space-composition-law.md', 'place': 'Proof, Step 1: domains of the ordered affine-line comparisons; finite-level site and adjunction interfaces'}

### Returned Step 2

The finite-level twist in the preceding identification is the usual etale torsion twist at every $n$, including ramified stages. Indeed choose $r\geq1$ with $\ell^rA=0$. From [def-coefficient-twists-detailed] and clauses (2)--(3) of [lem-pur-twist-sheaf-locally-free], associativity of ordinary tensor gives
$$A(1)=\mathbb Z_\ell(1)\otimes_{\mathbb Z_\ell}A\cong(\mathbb Z_\ell(1)/\ell^r)\otimes_{\mathbb Z/\ell^r}A\cong\mu_{\ell^r}\otimes_{\mathbb Z/\ell^r}A.$$
These are rank-one locally free sheaves; this calculation uses no flatness of $A$ over $\mathbb Z/\ell^r$. Their powers give the same identification for the positive twists used here. It is compatible with pullback because roots of unity and all the displayed tensor constructions pull back. Thus the finite torsion trace construction with annihilator $\ell^r$ is exactly the twist convention in the affine-line comparison of [def-pur-affine-line-purity-comparison]. No divisibility assumption on $n$ by the ramification index is introduced.

Uses: def-coefficient-twists-detailed, lem-pur-twist-sheaf-locally-free, def-pur-affine-line-purity-comparison

Source: {'document': 'literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-an/prop-pur-affine-space-composition-law.md', 'place': 'Proof, Step 1: identification of the finite coefficient Tate factors'}

### Returned Step 3

Obtain the coherence of $c$ from adjunctions. For $X\xrightarrow f Z\xrightarrow g Y$, use the composite adjunction [def-weil-pbc-composite-adjunction], whose counit is $\varepsilon_g\circ Rg_!(\varepsilon_f)$. The mate of $\alpha_{g,f}:Rg_!Rf_!\xrightarrow{\sim}R(gf)_!$ from [thm-sf-comp-composition] identifies its right adjoint with $Rf^!Rg^!$ and is $c_{g,f}$. Pasting along the adjunctions in clause (2) of [lem-weil-pbc-mate-pasting] shows that the two $c$-composites for three arrows are the mates of the two $\alpha$-composites. Those are equal by the associativity clause of [thm-sf-comp-composition]; the mate correspondence is a bijection, so the $c$-composites agree. When one arrow is an identity, the direct-image composition map is the identity by [thm-sf-comp-composition], and its mate is the identity of the right adjoint by clause (4) of [lem-weil-pbc-mate-pasting]; hence the corresponding $c$ is the unit identification. Pullback composition uses [lem-weil-pbc-proetale-derived-pullback-composition]; on constant coefficient sheaves it is termwise inverse-image composition. Tensor reassociation is that of the tensor powers defining the twists. This supplies the coherence actually needed when parentheses in the tower are changed.

Uses: def-weil-pbc-composite-adjunction, thm-sf-comp-composition, lem-weil-pbc-mate-pasting, lem-weil-pbc-proetale-derived-pullback-composition, def-coefficient-twists-detailed

Source: {'document': 'literature/stacks-project/categories.tex', 'place': 'Lemma 0DV0 (lemma-compose-counits), Lemma 0B65 (lemma-transformation-between-functors-and-adjoints); applied to blueprint Proof, Step 2'}

### Returned Step 4

Prove the displayed composition identity by induction on the length of the first block. Abbreviate $F_f(M)=Lf^*M(a)[2a]$ for an $a$-coordinate projection. In the ordered tower [def-pur-affine-space-comparison], appending one line $u$ replaces $\Gamma_{g,K}$ by
$$c_{g,u}^{-1}\circ\gamma_{u,Rg^!K}\circ F_u(\Gamma_{g,K}),\qquad\Gamma_{\mathrm{id},K}=\mathrm{id}_K.$$
The assertion for a first block of length one is exactly this recursion. Suppose it holds for a first block $f$ of length $a$, and append $u$. Substitute $\Gamma_{gf,K}=c_{g,f}^{-1}\gamma_{f,Rg^!K}F_f(\Gamma_{g,K})$ into the recursion. Naturality of $\gamma_u$ moves $F_u(c_{g,f}^{-1})$ across $\gamma_u$. Here naturality follows directly by transposing the natural projection-formula composite in [def-pur-affine-line-purity-comparison], with the natural projection map of [lem-weil-finite-compact-projection-formula]. The resulting two consecutive $c^{-1}$ maps equal the reassociated ones by Step 3. The remaining factors $\gamma_u F_u(\gamma_f)$ are precisely $\gamma_{fu}$ at $Rg^!K$. This proves the induction step. Taking the two block lengths to be $d,e$ gives exactly the equality in the statement, with source $Lp_{d+e}^*K(d+e)[2d+2e]$ and target $Rp_{d+e}^!K$. This argument concerns regrouping a fixed ordered list; coordinate interchange is established separately below.

Uses: def-pur-affine-space-comparison, def-pur-affine-line-purity-comparison, lem-weil-finite-compact-projection-formula, lem-weil-pbc-mate-pasting, thm-sf-comp-composition

Source: {'document': 'literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-an/prop-pur-affine-space-composition-law.md', 'place': 'Proof, Steps 1--2: induction spelling out the reassociation of the ordered tower'}

### Returned Step 5

Let $L_Y=\mathbf A^1_Y$, $a:L_Y\to Y$, $T=A_{L_Y}(1)[2]$, $U=Ra_!T$, and $t:U\to A_Y$ the line integration of [def-pur-affine-line-purity-comparison]. It is compatible with change of base. To check the specific map, use its defining compactification $a=qj$, and put $\bar T=A_{\mathbf P^1_Y}(1)[2]$, so $j^*\bar T=T$: the trace $t_q$ and its normalized counit commute with base change by [lem-asd-ordinary-finite-p1-adjunction], applied with annihilator $\ell^r$ from Step 2. The open-extension comparison is [lem-weil-pbc-etale-shriek-base-change-modules], and the compact-support exchange and its pasting are [thm-cbc-finite-torsion]. Applying these to the open-adjunction counit followed by the projective trace, $Rq_*j_!j^*\bar T\to Rq_*\bar T\xrightarrow{t_q}A_Y$ yields, for a morphism $v:Y'\to Y$ between separated finite-type $k$-schemes (hence between Noetherian schemes), the equality
$$v^*t=t'\circ\operatorname{Ex}_!:\ v^*Ra_!T\longrightarrow A_{Y'}.$$
The module open-extension comparison is applied termwise here; $T$ is a shifted locally free sheaf and inverse image and extension by zero are exact. The transport of Step 1 gives the identical equality at the finite pro-etale stage. In particular every line trace in a product tower is the pullback of this one $t$.

Uses: def-pur-affine-line-purity-comparison, lem-asd-ordinary-finite-p1-adjunction, lem-weil-pbc-etale-shriek-base-change-modules, thm-cbc-finite-torsion

Source: {'document': 'literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-an/prop-pur-affine-space-composition-law.md', 'place': 'Proof, Steps 3--4: base-change identity for the line trace needed to compare the two coordinate towers'}

### Returned Step 6

Write $X_m=L_Y^{\times_Ym}=\mathbf A^m_Y$, $T_m=A_{X_m}(m)[2m]$, $F_mK=p_m^*K\otimes^LT_m$, and let $\tau_{m,K}:Rp_{m!}F_mK\to K$ be the exceptional transpose of the ordered $\Gamma_{m,K}$. Put $I_m=\tau_{m,A_Y}$; these are temporary morphisms in this proof. For a tower $f,g$, the composite-adjunction formula of Step 3 says that the transpose of $c_{g,f}^{-1}\gamma_{f,Rg^!K}F_f(\Gamma_{g,K})$ is
$$\varepsilon_{g,K}\circ Rg_!(\varepsilon_{f,Rg^!K})\circ Rg_!Rf_!\bigl(\gamma_{f,Rg^!K}\circ F_f(\Gamma_{g,K})\bigr).$$
Combining the middle two factors first gives $Rg_!\tau_{f,Rg^!K}\circ Rg_!Rf_!F_f(\Gamma_{g,K})$. Naturality of $\tau_f$ changes this to $Rg_!(\Gamma_{g,K})\circ Rg_!(\tau_{f,F_gK})$. The full transpose is therefore
$$\tau_{g,K}\circ Rg_!(\tau_{f,F_gK}).$$
For a line, its definition is $\tau_{1,K}=(1_K\otimes t)\circ\mathrm{PF}^{-1}$. Induction using this pasted formula and the composition pentagon and naturality of [prop-sf-pf-coherence] now gives
$$\tau_{m,K}=(1_K\otimes I_m)\circ\mathrm{PF}_{p_m}^{-1}:Rp_{m!}(p_m^*K\otimes^LT_m)\longrightarrow K.$$
Specifically, two successive inverse projection maps identify the pasted source with $K\otimes Rp_{m!}T_m$ by that pentagon; naturality moves $1_K$ past the inner trace, leaving the very same pasted map evaluated at $K=A_Y$, namely $I_m$. This proves the asserted formula and does not assume any coordinate invariance.

Uses: def-pur-affine-space-comparison, def-pur-affine-line-purity-comparison, def-weil-pbc-composite-adjunction, lem-weil-pbc-mate-pasting, lem-weil-finite-compact-projection-formula, prop-sf-pf-coherence

Source: {'document': 'literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-an/prop-pur-affine-space-composition-law.md', 'place': 'Proof, Steps 2--4: explicit counit calculation reducing equality of comparisons to equality of integration maps'}

### Returned Step 7

First verify the one-factor object needed for the product-domain induction. Apply [lem-amb-affine-space-top-trace] only with $S=Y$, $d=1$, and $N=\ell^r$ from Step 2. The ring $A$ is finite with $NA=0$, $N$ is invertible since $\ell\ne p$, and $Y$ is Noetherian by Step 1. Its bounded-below input is $A_{\mathbf A^1_Y}(1)[2]$. The source of its isomorphic counit is the ordinary etale representative of $U$. Step 2 identifies its twist, and [lem-sf-class-compact-support-comparison] realizes this object on the pro-etale site, giving $U\cong A_Y$. This is only an object isomorphism; no identification of $I_m$ with a higher-dimensional top-trace counit is used.

Uses: lem-amb-affine-space-top-trace, lem-sf-class-compact-support-comparison

Source: {'document': 'literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-an/prop-pur-affine-space-composition-law.md', 'place': 'Proof Steps 3--4, as expanded in returned split Step 7: extracted product-domain and actual-integration arguments'}

### Returned Step 8

Apply [lem-pur-affine-space-product-domain] to $B=Y$, $f=a:L_Y\to Y$, $M=T=A_{L_Y}(1)[2]$ and the object isomorphism $U\cong A_Y$ just obtained. The source coefficient is bounded constructible of finite Tor amplitude because it is a shifted rank-one locally free Tate sheaf, by [prop-weil-twist-preserves]. Its relative external powers are $T_m$ by tensor-power additivity and the even shift identifications. The cited lemma supplies $V_m\cong A_Y$, Tor amplitude $[0,0]$, and all the typed canonical binary product isomorphisms $\kappa_{m,1}$. In particular the coefficient $V_m$ has its required finite Tor amplitude before the second projection formula is invoked; this is the original object induction, now a separate node.

Uses: lem-pur-affine-space-product-domain, prop-weil-twist-preserves

Source: {'document': 'literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-an/prop-pur-affine-space-composition-law.md', 'place': 'Proof Steps 3--4, as expanded in returned split Step 7: extracted product-domain and actual-integration arguments'}

### Returned Step 9

The base-change identities of Step 5 hold over every separated finite-type base used in the tower; Step 6 identifies $I_m$ with the exceptional transpose specified in [lem-pur-affine-space-trace-factorization]. Its finite-Tor hypothesis is now Step 8, so that lemma gives
$$I_1=t,\qquad I_{m+1}=(I_m\otimes t)\kappa_{m,1}.$$
Define $\kappa_1=1_U$ and $\kappa_{m+1}=(\kappa_m\otimes1_U)\kappa_{m,1}$. Induction substitutes $I_m=t^{\otimes m}\kappa_m$ into the binary equality, giving $I_{m+1}=t^{\otimes(m+1)}\kappa_{m+1}$, with tensor units suppressed. This substitution uses only functoriality of tensor. Clause (ii) of [lem-sf-kunneth-coherence] identifies every parenthesization with this same iterated product, and clause (iv) supplies its projection-formula identification.

Uses: lem-pur-affine-space-trace-factorization, lem-sf-kunneth-coherence

Source: {'document': 'literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-an/prop-pur-affine-space-composition-law.md', 'place': 'Proof Steps 3--4, as expanded in returned split Step 7: extracted product-domain and actual-integration arguments'}

### Returned Step 10

For an adjacent transposition of the $m$ line factors, the symmetry clause of [lem-sf-kunneth-coherence] identifies the induced map on $Rp_{m!}T_m$ with the corresponding symmetry of $U^{\otimes m}$. Tensor naturality gives
$$(t\otimes t)\circ\sigma_{U,U}=\sigma_{A_Y,A_Y}\circ(t\otimes t)=t\otimes t,$$
since the symmetry of two tensor units is the identity. On the source, the tensor sign symmetry of [def-kun-derived-tensor] is $x\otimes y\mapsto(-1)^{ij}y\otimes x$; for $T=A(1)[2]$ the two degrees are $-2,-2$, so the sign is $+1$. Locally choose a generator $b$ of the rank-one twist [prop-weil-twist-preserves]; the unshifted interchange sends $b\otimes b$ to itself, and consequently is the identity under the twist-additivity identification. For blocks of sizes $d,e$, interchange sends $b^{\otimes d}\otimes b^{\otimes e}$ to $b^{\otimes e}\otimes b^{\otimes d}$; both identify with $b^{\otimes(d+e)}$, and the shift sign is $(-1)^{(-2d)(-2e)}=+1$. It follows from Step 9 that each adjacent coordinate transposition preserves $I_m$, and hence that every coordinate permutation does. By the projection-formula compatibility in [lem-sf-kunneth-coherence] and Step 6 it preserves $\tau_{m,K}$ for every $K$, without moving $K$ past a shifted coordinate factor. Finally the exceptional Hom bijection of [thm-sf-ambient-adjoint-class] is injective and natural, so equality of these transposes proves equality of the two transported comparisons. Combined with Step 4 this gives the asserted composition law and equality for the two block orderings.

Uses: lem-sf-kunneth-coherence, def-kun-derived-tensor, prop-weil-twist-preserves, thm-sf-ambient-adjoint-class

Source: {'document': 'literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-an/prop-pur-affine-space-composition-law.md', 'place': 'Proof, Steps 3--4: explicit Koszul sign and naturality calculation for coordinate permutations'}

## Dry-run repair

The first complete dry run found that a combined bracket [def-a, def-b] is not recognized as either node citation. I separated the two actual definition citations in the abstract node (and the one combined pair in the product node), leaving the mathematical statement unchanged, and refreshed the verbatim quotes. The warnings about the three off-unit tools are covered by split_report.tool_uses and the explicit scope checks above.
