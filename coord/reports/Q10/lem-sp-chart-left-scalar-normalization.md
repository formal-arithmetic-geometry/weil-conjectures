# Worker report: lem-sp-chart-left-scalar-normalization

1. Files written: the item at dag/nodes/sec-smooth-purity/lem-sp-chart-left-scalar-normalization.json, retaining its statement and statement dependencies, plus three statement-only children in the same directory:
   - lem-sp-chart-normalized-model-identification: statement, unsplit; no Mathlib match.
   - lem-sp-chart-sum-affine-counit-transport: statement, unsplit; no Mathlib match for the geometric model identification and coherence (formal adjunction transport is in Mathlib).
   - lem-sp-scalar-compositor-replacement-pasting: statement, unsplit; no direct Mathlib match for the combined replacement/compositor identity and independent model changes.
   Also report.md and citations.json. No Lean or repository files were written. Three new nodes, zero Mathlib leaves. Each new node has empty proof/proof_deps and null proof_origin. The item has four assembly steps totalling 2110 characters, below 3000.
2. Attachments: none. The item tag and notion searches in lean/WeilConjectures do not give an exact closed declaration. The existing declarations in lean/Sheaf/Paper/ChartLeftScalarNormalization.lean include sorry proofs for the coefficient square, refinement, model identification and counit; they are not attachments. Existing Lean metadata is preserved.
3. WANTED: none. The blueprint, Stacks source and Mathlib source used here are available locally.
4. The prior sandbox report declined the assignment because the live node had an accepted Q02 split. The newer explicit human return reopens that same split and requires at least two new comparable statement-only children. That instruction supersedes the earlier generic no-re-split rule for this item. I copied the current live item, including the reviewer's corrected graph-datum recognition in old Step 1. The previous report is retained under research/previous-attempt-report.md. The repair is substantive: three new proof tasks and a new assembly, not a rebase or unchanged push. No disputed statement or changed target is involved.
5. Remaining work is precisely proving the three unsplit child statements in future workers. This delivery intentionally supplies no child proofs, as required by the return. Nothing is abandoned.

## Repair coverage and distribution

The three child statements have respectively 2099, 2408 and 2074 characters. They are separate arguments rather than one restatement of the original theorem. The model-identification node is more general in the second map and has no coefficient extension; the counit node has one ring and the ordered geometric adjunction, without the coefficient equation; the replacement-pasting node is about arbitrary categories and possibly noninvertible natural transformations, without schemes or purity. The item supplies the actual geometric substitution.

Old Step 1: preservation of the finite-Tor domain remains the direct existing-domain citation in new Step 1. All remaining content (existence of the canonical graph-normalized family as a datum, recognition of its sheaf-level graph map and derived-unit formula, matching the canonical coefficient-comparison family, and independent-model agreement with the restricted-closure construction) becomes lem-sp-chart-normalized-model-identification. Its statement explicitly includes the datum conditions instead of silently claiming that an arbitrary isomorphism supplies them.

Old Step 2: the specified ordered affine and sum adjunctions, composition of their Hom bijections, precomposition by lambda and its inverse, the resulting actual counit formula and its agreement with the specified chart are assigned to lem-sp-chart-sum-affine-counit-transport. Its model-change assertions also carry the last part of old Step 5. The proof task includes the concrete ordered affine adjunction, its specified compactification transports and the dimension-zero identity, not merely an abstract existence of some adjunction.

Old Steps 3 and 4: the inverse c-square and all four lines of the naturality/composition calculation become the first conclusion of lem-sp-scalar-compositor-replacement-pasting. The hypotheses there are the exact canonical sum and composition equations furnished by lem-sp-et-proet-coefficient-compatibility, with beta allowed to be noninvertible.

Old Step 5: the comparison/cocycle identifications for changes of g, e and p_d are included in the model-identification child; the cancellation of the e comparison, movement of the p_d source comparison and g target comparison, and transport of the coefficient equation are included as the second-system conclusion of the replacement-pasting child. The counit formula epsilon'_g rho_g = epsilon_g and the constituent composite-counit transport are included in the counit child. New Step 4 applies these statements with the actual coefficient refinement squares. No compactification-change case has been dropped.

## Sources and searches

For all four node files I read literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, the Charts paragraph (the sum counit, ordered affine integration and scalar compatibility), the current item proof, the chapter record and sk-lem-sp-reduction unit record. These children expand that chart route; no chapter or unit record changes. The source is agent-written blueprint material, so the item's proof_origin remains agent. The precise new tasks also record their old-step locations. The old proof is preserved verbatim below for the next workers.

Underlying source checks: Stacks 03S3 is etale-cohomology.tex, definition-extension-zero; 03S5 is proposition-describe-jshriek in the same file. They give the sum-extension construction and geometric-stalk description. Stacks 0F7J is more-etale.tex, lemma-shriek-composition; 0GL6 is remark-Rf-lower-shriek-change-of-rings. They support compact-support composition and derived coefficient changes. They do not by themselves assert this full named chart normalization; the exact DAG statements supply the canonical comparisons. No SGA route is used.

Before naming the children I searched the full DAG by graph normalization, restricted closure, chart comparison, counit transport, replacement, scalar compositor, pasting and the relevant declarations; tools/blueprint_refs.py search was run with chart comparison, composite counit, coefficient square, graph-normalized, pasting, adjunction transport, normalized chart, scalar compositor, replacement and compact-support comparison. The nearest ancestor is det-sp-reduction-exceptional. The new nodes have that ancestor with via [lem-sp-chart-left-scalar-normalization], precise places and same_as []. No searched blueprint statement states any of the three complete child propositions.

All Mathlib queries were actually run using msearch.py and retained in searches.jsonl. Each child records LeanFinder twice, Loogle, LeanSearch and grep. I read the actual hits and the relevant source: Adjunction.Basic lines 497–519 (ofNatIsoLeft, Hom and counit formulas), lines 567–587 (comp and its counit/Hom formula), Whiskering lines 243–303 (iso whiskering and interchange), and Functor/TwoSquare (the square definition, whiskerings and hComp/vComp). These are formal ingredients, not the geometric model recognition or the complete replacement/compositor identity with three independently changed models. CatCommSq results concern invertible square cells, whereas the new categorical lemma assumes no inverse of beta. The grep using the single-file subpath returned malformed file/line labels from the fixed search script; I preserved that output exactly and read the file directly, without claiming a leaf or inventing a line number. All searches are recorded as they ran; no service was unavailable during these queries.

## Not duplicates

lem-sp-chart-normalized-model-identification vs lem-asd-etale-compact-support-normalization: the latter constructs the etale compact-support/sum comparison; the child proves it supplies every field of the stronger graph-normalized datum and identifies the independently chosen chart models with the restricted-closure definition.
lem-sp-chart-normalized-model-identification vs def-sp-etale-compact-support-normalization: the existing node only defines the datum and explicitly asserts no existence; the child asserts the canonical family realizes it.
lem-sp-chart-normalized-model-identification vs def-sp-etale-adjoint-chart-comparison: the definition chooses a restricted-closure formula from a datum; the child identifies the general three-model formula with it and gives its simultaneous model-change equation.
lem-sp-chart-normalized-model-identification vs lem-amb-etale-compact-comparisons: the existing theorem supplies generic compact-support composition, not the normalized sum replacement or recognition of the restricted-closure chart map.
lem-sp-chart-sum-affine-counit-transport vs lem-sp-chart-finite-ring-adjunction: the existing broader etale/pro-etale adjunction theorem relies on the present parent; the child isolates the ordinary-site ordered composition Hom bijection and explicit counit for all chosen models, without invoking that downstream theorem.
lem-sp-chart-sum-affine-counit-transport vs lem-sp-chart-counit-scalar-transport: that theorem is a downstream coefficient-counit identity for two rings and both sites; the child constructs the one-ring ordinary chart counit and its model-change formula.
lem-sp-chart-sum-affine-counit-transport vs lem-amb-affine-space-top-trace: the latter is the affine adjunction alone, without an etale chart factor or its independent-model counit normalization.
lem-sp-chart-sum-affine-counit-transport vs lem-cat-equivalence-right-adjoint-counit-transport: the latter changes categories by an equivalence and compares existing right adjoints; it does not give the ordered geometric composite chart with fixed right functor and all compactification changes.
lem-sp-scalar-compositor-replacement-pasting vs lem-amb-natural-transformation-whisker-exchange: interchange is one naturality identity; the child supplies the inverse replacement square, replaced compositor square and simultaneous F/P/Q model-change equations.
lem-sp-scalar-compositor-replacement-pasting vs lem-sp-exact-derived-transformation-pasting: the existing node transfers established ordinary equalities to derived categories; the child establishes different ordinary categorical equalities without exactness or localization hypotheses.
lem-sp-scalar-compositor-replacement-pasting vs lem-pur-adjoint-equivalence-conjugation-calculus: that node conjugates functors through adjoint equivalences of categories; the child keeps all categories fixed and changes a factor inside a compositor with noninvertible coefficient cells.
lem-sp-scalar-compositor-replacement-pasting vs lem-pur-expression-counit-substitution-coherence: that node concerns recursive normalized semilinear-system expressions and reduction counits, absent from the child.
lem-sp-scalar-compositor-replacement-pasting vs lem-pur-etale-open-scalar-composition: the existing theorem is open-immersion scalar composition, whereas the child proves a generic replacement-compositor and model-change calculus.
lem-sp-scalar-compositor-replacement-pasting vs lem-sp-et-proet-coefficient-compatibility: the existing geometric theorem supplies beta's composition/refinement and canonical sum square, which are hypotheses of the child; it does not perform replacement by E and the resulting model-change cancellation.

## Review by Q10

I checked B–E of delivery-errors against the actual statements, not just their dependency names. The children introduce their own rings, schemes or categories, all functors and maps and the orientations of their formulas. Every child is unsplit with no proof sketch in its statement. The return's requirement to spread the old proof overrides the general preference to keep short formal calculations inline here: the categorical child includes the full compositional and three-model calculation, not a two-line inverse square alone. The other two children have comparable independent proof burdens. No child simply repeats all conclusions of the original item, and none depends on the parent or its downstream chart-adjunction/scalar-counit theorem.

For new Step 1, I opened lem-sp-etale-ctf-chart-domain: its statement explicitly says F_h and T preserve D^b_ctf, and that inverse image/Tate powers/shifts do too. The new model-identification child's statement gives both the existence/recognition of the graph datum and lambda's exact restricted-closure/model formula. The standing finite-type field hypotheses imply Noetherian schemes; the given compactifications have standing middle schemes. Bounded complexes lie in D^+, the exact domain of the existing compositor theorem. Thus its bounded-below comparison is not silently applied on all unbounded complexes.

For new Step 2, I checked the counit child's statement contains the precise ordered affine adjunction, the degreewise sum adjunction, precomposition by lambda, and epsilon_d F_d(v) lambda^{-1}. Here N is invertible on Y because N is a power of ell different from char(k); both finite rings are annihilated by it. H preserves the finite-Tor domain by Step 1's actual cited domain theorem. The identity epsilon_g lambda_H = delta follows by cancellation, with neither direction reversed. The child's ordered construction precludes an arbitrary new trace.

For new Step 3, I read the entire statement of lem-sp-et-proet-coefficient-compatibility. Its last square is c_{e,B} beta_e = sigma_e T(c_{e,A}); its composition formula has beta_d evaluated at F_e(input), precisely the hypothesis for categorical replacement. The model-identification child pins down the same canonical family, preserving the Q02 reviewer's correction. Every transformation in the substitution is between the stated categories. The replacement child's first equation is obtained by cancelling c_B on the left and T(c_A) on the right; its second equation uses naturality of beta_P at c_A^{-1}. All arrows point from T_Y F_{d,A} E_A to F_{g,B} T_U. No beta inverse is needed, hence no hidden flatness or projective-dimension condition.

For new Step 4, I checked each source of refinement data explicitly. The model-identification child supplies c'_e rho_e = c_e and lambda' (rho_d E) = rho_g lambda. The existing coefficient-compatibility statement supplies beta'_h T(rho_{h,A}) = rho_{h,B}T beta_h, including comparison through any common refinement. These are exactly the second-system hypotheses in the replacement child. Its conclusion compares both source and target, rather than asserting unspecified transport. The counit child's last paragraph supplies epsilon'_g rho_{g,H} = epsilon_g and delta' (rho_d E)H = delta, so cancellation of the refinement comparisons retains the actual counit. The common-refinement cocycle clauses are explicit in both geometric children.

Small-case checks: d=0 gives the identity affine adjunction; e=id gives the normalized identity sum comparison; identity coefficient extension makes the categorical coefficient square an identity/naturality square. For empty U, all assertions remain natural-transformation identities with zero compact-support input. The unital non-flat map Z/ell^2 -> F_ell is allowed throughout: no calculation uses a beta inverse. The general categorical statement also allows empty categories. If all model comparisons are identities, its model-change equations reduce to the original equations; if only F changes its rho cancels, if only P changes the rho sits at the source, and if only Q changes it sits at the target. These tests confirm all displayed orientations.

citations.json has one entry for each step/node pair. I constructed every quote as a literal substring of that node's statement and checked substring membership. I preserved the old proof below in full so each future child worker can recover the arguments the re-split distributes. No new parent step is longer than 2000 characters. The server-side review_split command passed. Full dry-run and delivery results are recorded at the end after execution.

## Original argument, preserved verbatim

The following is the live Q02 proof used as the returned baseline, including the maintainer's datum-recognition correction. It is research material for the unsplit children, not proof steps on those new nodes.

### Old Step 1

Work on the ordinary etale site, as in the asserted equation. By [lem-sp-etale-ctf-chart-domain], each $F_{h,R}$ and coefficient extension preserves the indicated finite-Tor categories. By [lem-asd-etale-compact-support-normalization], $c_{e,R}:F_{e,R}\simeq E_R$ is the canonical refinement-compatible isomorphism, so $E_R$ also preserves this category. The composition comparison $\alpha_R$ is an isomorphism by [lem-amb-etale-compact-comparisons]. Hence $\lambda_R=\alpha_RF_{d,R}(c_{e,R}^{-1})$ is an isomorphism. Take the datum of [def-sp-etale-compact-support-normalization] entering [def-sp-etale-adjoint-chart-comparison] to be the family $c_{v,c}$ of [lem-asd-etale-compact-support-normalization]: its degree-zero sum-component description gives the graph-extension condition and the derived formula for $c^{-1}$, and its proper-refinement agreement, base-change square with identity and composition normalization, and counit identification are the remaining conditions of the datum. So the comparison $c_e$ used here is the one that enters [lem-sp-et-proet-coefficient-compatibility] in Steps 3–5. The specified chart comparison of [def-sp-etale-adjoint-chart-comparison] uses a compatible restricted-closure compactification; refinement compatibility of $c_e$ and composition identifies it with this same formula for the independently chosen compactifications.

Uses: lem-sp-etale-ctf-chart-domain, lem-asd-etale-compact-support-normalization, lem-amb-etale-compact-comparisons, def-sp-etale-adjoint-chart-comparison, def-sp-etale-compact-support-normalization, lem-sp-et-proet-coefficient-compatibility.

### Old Step 2

Write $G_{d,R}=p_d^*(-)(d)[2d]$, $H_R=e_R^*G_{d,R}$, and let $v_R:E_Re_R^*\to\mathrm{id}$ be the sum/evaluation counit. The affine adjunction is the ordered one of [lem-amb-affine-space-top-trace], and the sum adjunction is specified by [def-sp-etale-adjoint-chart-comparison]. By the explicit composite-adjunction formula [def-weil-pbc-composite-adjunction], the counit for $L_R=F_{d,R}E_R\dashv H_R$ is $\delta_{R,K}=\epsilon_{d,R,K}\circ F_{d,R}(v_{R,G_{d,R}K})$. Transfer its Hom bijection to $F_{g,R}$ by sending $a:F_{g,R}M\to K$ first to $a\circ\lambda_{R,M}:L_RM\to K$, then to its composite adjunct. Precomposition with $\lambda_R$ is a natural bijection, with inverse precomposition with $\lambda_R^{-1}$. Evaluating the resulting Hom bijection at the identity of $H_RK$ gives the counit $\epsilon_{g,R,K}=\delta_{R,K}\circ\lambda_{R,H_RK}^{-1}$, so $\epsilon_{g,R,K}\circ\lambda_{R,H_RK}=\delta_{R,K}$. This is precisely the chart adjunction obtained using the specified left comparison. It retains the actual sum-then-affine counit, rather than choosing a new trace.

Uses: lem-amb-affine-space-top-trace, def-sp-etale-adjoint-chart-comparison, def-weil-pbc-composite-adjunction.

### Old Step 3

For $M\in\mathcal C_{U,A}$, [lem-sp-et-proet-coefficient-compatibility] gives $c_{e,B,T_UM}\circ\beta_{e,M}=\sigma_{e,M}\circ T_V(c_{e,A,M})$. Compose on the left with $c_{e,B,T_UM}^{-1}$ and on the right with $T_V(c_{e,A,M}^{-1})$. Functoriality and cancellation yield
$$\beta_{e,M}\circ T_V(c_{e,A,M}^{-1})=c_{e,B,T_UM}^{-1}\circ\sigma_{e,M}.$$
This uses the stated graph-normalized comparison, not an arbitrary isomorphism from $F_e$ to sum extension.

Uses: lem-sp-et-proet-coefficient-compatibility.

### Old Step 4

Apply the composition equation of [lem-sp-et-proet-coefficient-compatibility] to $(e,p_d)$, and then naturality of $\beta_d$ at $c_{e,A,M}^{-1}:E_AM\to F_{e,A}M$. Suppressing only component subscripts, the resulting calculation is
$$\begin{aligned}
\beta_gT_Y(\lambda_A)
&=\alpha_BT_U\,F_{d,B}(\beta_e)\,\beta_dF_{e,A}\,T_YF_{d,A}(c_{e,A}^{-1})\\
&=\alpha_BT_U\,F_{d,B}\bigl(\beta_e\circ T_V(c_{e,A}^{-1})\bigr)\,\beta_dE_A\\
&=\alpha_BT_U\,F_{d,B}(c_{e,B}^{-1}T_U)\,F_{d,B}(\sigma_e)\,\beta_dE_A\\
&=\lambda_BT_U\,F_{d,B}(\sigma_e)\,\beta_dE_A.
\end{aligned}$$
The third line is Step 3. Every arrow is $B$-linear with source $T_YF_{d,A}E_A$ and target $F_{g,B}T_U$; in particular no inverse of $\beta_d$ and no flatness of $B$ over $A$ has been used.

Uses: lem-sp-et-proet-coefficient-compatibility.

### Old Step 5

For another specified compactification of $g$, write $\rho_R:F_{g,R}\simeq F'_{g,R}$ for the canonical common-refinement comparison. Coherence of composition in [lem-amb-etale-compact-comparisons] gives $\lambda'_R=\rho_R\lambda_R$. The refinement square of [lem-sp-et-proet-coefficient-compatibility] says $\beta'_gT_Y(\rho_A)=\rho_BT_U\,\beta_g$. Thus the left side of Step 4 for $\lambda'$ is $\rho_BT_U$ times its old left side, and its right side is $\rho_BT_U$ times its old right side. For a change of the compactification of $e$, refinement compatibility in [lem-asd-etale-compact-support-normalization] gives $c'_e\rho_e=c_e$, so $\rho_e$ cancels in $\alpha'F_d((c'_e)^{-1})$. For a change of the compactification of $p_d$, naturality and coherent composition give $\lambda'_R\circ(\rho_{d,R}E_R)=\lambda_R$; its coefficient square is the same refinement square, now for $p_d$, whiskered by $E_A$. These identities prove the equation for every set of choices. The transported counit formula in Step 2 likewise becomes $\epsilon'_g=\epsilon_g\rho_H^{-1}$ under a change of $g$; substituting $\lambda'=\rho\lambda$ cancels $\rho_H^{-1}\rho_H$. Changes of the two constituent models are already the adjunction-preserving identifications used to define the ordered affine adjunction and the graph-normalized sum comparison. Common-refinement independence and the cocycle law make these identifications independent of the refinement chosen.

Uses: lem-amb-etale-compact-comparisons, lem-sp-et-proet-coefficient-compatibility, lem-asd-etale-compact-support-normalization.

## Validation

The server-side review_split check passed. The full deliver.py --no-push invocation exited 0 and printed preflight passed / OK (not pushed), candidate 18666c3c3dc. It checked the DAG, assembly, new-node searches and literal citations on the server. The following final dry run includes this validation note. No Lean compiler or Lake command was run.
