# Repair report: lem-pod-global-duality-map-identification

1. Files written: the item (statement unchanged; split, no Mathlib match), plus the following three statement-only unsplit nodes, each with two semantic phrasings, LeanSearch, Loogle, and source grep actually run and logged:
   - lem-pod-structure-hom-chain-realization: statement; no Mathlib match.
   - lem-pod-point-integral-evaluation-normalization: statement; no Mathlib match.
   - lem-pod-point-field-evaluation-normalization: statement; no Mathlib match.
   Supporting deliverables: citations.json and this report. Search output files and searches.jsonl retain the actual results.
2. Attachments: none. The project has tensor–Hom and global-duality constructions, but not this all-four-stage map-normalization assertion. In particular PoincarePairing.lean explicitly says that identification with the inverse global map is not formalized. GlobalDuality.lean works on small-etale derived sheaves and does not supply the completed integral and common-stage point-evaluation comparison.
3. WANTED: none. The source proof is the local blueprint and the retained mathematical expansions are explicitly agent-written, not attributed to an unavailable reference.
4. The return concerns workload, not a wrong statement. The sandbox initially held only .brief marker files; its claimed retained nodes/report were absent. I recovered the seven-step returned proof and all existing metadata from the read-only repository, without any git command. There was no sandbox report or searches.jsonl to discard or rerun. The main statement is unchanged byte for byte. I did not edit a target, unit, chapter, existing lower node, Lean file, repository file, or launcher script.
5. Unfinished work: proofs of the three new nodes, deliberately left statement-only for separate workers as requested. No other mathematical argument is omitted: the complete returned argument is reproduced below, with its allocation and dependencies. Delivery validation is recorded at the end after the required run.

## Return repair and allocation of work

The single numbered demand was to replace a 9146-character proof by at most 3000 characters of assembly and at least three comparable, independently assignable unsplit nodes. The parent now has five short steps. The work is distributed as follows:

- New structure-hom-chain-realization: old steps 1–2, including every coefficient-stage domain check, the representing inverse argument with both identity equations, agreement with both source chains, and naturality in N.
- New point-integral-evaluation-normalization: old steps 4–5, including exactness and coefficient sections, the finite quotient computation, actual reconstruction counit, K-flat/K-injective comparison, completed perfect model and signed evaluation, and j = kappa F(rho).
- New point-field-evaluation-normalization: old step 6, including the explicit scalar-Hom map, the sign check, torsion integral lattices, localized morphisms and their sums, and common-stage compatibility with identities/towers.
- Parent steps 2 and 5 retain old steps 3 and 7: identify the structure mate, use naturality to normalize the exchange, identify the constructed global map and cancel inverses. None of the three new nodes states the global-map equality or the whole item. The exact old arguments are retained below rather than compressed away.

## Sources and duplicate searches

I read the current chapter and sk-thm-sf-package unit, respecting clause (6)'s tensor–Hom, Verdier exchange and global-duality route. I read main-20261015 thm-pod-identification-of-the-comparison.proof.md (the five Hom bijections and third paragraph), fix-lem-tensor-adjunction.proof.md Step 1, lem-sf-tensor-hom.proof.md Steps 1–2, fix-cor-verdier-exchange.proof.md Steps 1–3, lem-pod-point-dualizing-complex.proof.md, and thm-pod-global-verdier-duality.proof.md. The latter two are short agent blueprint proofs; the report below preserves the expansions needed to make their map identifications explicit. No SGA source is used.

I searched all DAG statements and project Lean for the notions, exact item tag and candidate ids; I ran blueprint_refs ancestor and searches for Hom chain, counit formula, finite-Tor outputs, point-dualizing, evaluation transpose, point evaluation, coefficient dual and rationalized evaluation. Existing relevant lemmas were opened, not inferred from their titles. No blueprint node states any of the new strengthened map-identification assertions. Each new node has the nearest ancestor thm-pod-identification-of-the-comparison and the one-element via list through the item.

## Not duplicates

lem-pod-structure-hom-chain-realization vs lem-pod-hom-chain-counit-formula: the existing lemma computes the abstract Hom-chain image of t. The new lemma additionally discharges all-stage finite-Tor memberships for the represented objects and identifies both separately specified canonical geometric isomorphisms with that representing morphism. The 2761-character domain/representation argument, not merely a new name for the existing formula, is assigned here.

lem-pod-structure-hom-chain-realization vs lem-sf-tensor-hom and fix-lem-tensor-adjunction: these assert existence and naturality of their canonical isomorphisms, not equality with the displayed counit/projection transpose or its represented test-object action, nor the explicit all-stage membership assertion.

lem-pod-point-integral-evaluation-normalization vs lem-pod-point-sections-reconstruction: reconstruction is conditional on exactness and coefficient sections and says nothing about the evaluation transpose or j. The new node establishes those hypotheses in the actual finite/completed coefficient sheaves and identifies the specified dualizing map with evaluation on the reconstructed object. Unlike the previously dropped extension-counit-model node, it carries the entire finite/integral evaluation-normalization argument, not just reconstruction plus its routine specialization.

lem-pod-point-integral-evaluation-normalization vs lem-pod-point-derived-hom-evaluation and lem-pod-point-completed-evaluation: these are ordinary and completed model-computation ingredients. They do not identify the specified point-dualizing j on arbitrary constructible C with the tensor transpose through the actual reconstruction counit and all required coefficient hypotheses.

lem-pod-point-integral-evaluation-normalization vs lem-pod-point-dualizing-complex and lem-sf-point: those give the canonical point-dualizing isomorphism without the equality of the actual evaluation-transpose kappa with its coefficient-Hom model. That extra map normalization is exactly the work now isolated, for an arbitrary point C rather than only a compact-support direct image.

lem-pod-point-integral-evaluation-normalization vs lem-pod-point-tensor-hom-evaluation and lem-pod-point-hom-complex-adjunction: the latter are ordinary chain-model assertions assuming the explicit adjunction; neither establishes completed derived evaluation or the normalization of the geometric j.

lem-pod-point-integral-evaluation-normalization vs lem-sf-point-ringed-evaluation-model and def-sf-point-evaluation-derived-compatibility: ordinary tensor comparison and the definition of representative compatibility do not give internal duality or completed evaluation; the latter is a definition, not a theorem supplying it.

lem-pod-point-field-evaluation-normalization vs lem-pod-point-scalar-hom-evaluation: the latter normalizes the scalar-transition arrow on perfect integral models. The new node normalizes kappa and j themselves under rationalization, including torsion lattices and localized morphisms, and then descends that normalization to the common-stage category. It retains the whole rational calculation rather than restating only the scalar-transition lemma that an earlier reader correctly found duplicated.

lem-pod-point-field-evaluation-normalization vs lem-pod-point-duality-coefficient-compatibility: that node asserts a coefficient-change square for j; it does not identify kappa with the rationalized evaluation transpose or establish j = kappa F(rho). No new statement is merely that coefficient-change square.

lem-pod-point-field-evaluation-normalization vs lem-pc-base-change-rhom-perfect: the latter supplies only the coefficient-module scalar-Hom isomorphism, not its agreement with the specified point sheaf tensor/evaluation comparisons or common-stage j.

lem-pod-point-field-evaluation-normalization vs lem-sf-rational-slice-completed-evaluation: the latter concerns slice restriction on an arbitrary scheme and localization of a sheaf evaluation comparison, not sections into coefficient modules and point-dualizing normalization.

No new node cites a Stacks tag shared with an existing node. These nodes are source-specific refinements of the blueprint's map comparison, not newly invented commutative-algebra facts needing a Stacks attribution.

## Mathlib search assessment

For every new id the five recorded searches were actually run through msearch.py and the hit types were read. All services returned results successfully. The first node's hits were generic tensor–Hom equivalences and derived-adjunction counits; the second's were ordinary functor-category internal Hom, condensed evaluation and unrelated etale algebra; the third's were trace duals, module extension, evaluation and ordinary module dual base change. I read Mathlib/LinearAlgebra/Dual/BaseChange.lean lines 35–60: Module.Dual.baseChange_apply_tmul gives the module generator calculation, but no derived/sheaf/common-stage assertion. I also read the closed-functor comparison source: cartesian closed comparison is not this completed tensor comparison. No exact or one-line specialization establishes any new statement, so all three remain unsplit, not Mathlib leaves. Original searches in the item are retained unchanged; their question and conclusion did not change.

## Review by NH

I checked the return by reading each old step and every cited lower statement, then allocating each whole argument to a new task or the assembly. The structure lemma's source is the two explicitly written Hom chains, not just the names of their isomorphisms. Its N is any finite-Tor point object; the coefficient unit has amplitude [0,0], exceptional adjunction gives C and a!N, stability gives internal Homs and finite direct images, and the separate integral direct-image theorem supplies the completed ordinary image. Thus the Yoneda tests include both representing objects, without identifying finite Tor with site-perfectness. Its new statement preserves both source constructions and naturality in N. In particular the parent may substitute both the unit and the identity dualizing object.

Parent step 1 cites precisely this new statement for domains, the canonical alpha and naturality. Parent step 2 cites point-dualizing-complex for u and identity adjunction, structure-identity-mate for m = a!u (which its statement explicitly asserts), and fix-cor-verdier-exchange for the canonical exchange; the source proof specifies that exchange as the inverse Hom map followed by the mate. Substituting the naturality equality from step 1 proves its formula, not an appeal to an unnamed naturality claim. I checked the direction of every arrow: A(u)alpha_w inverse maps D_s C to D, while rho maps D_s C to H.

For the finite/integral node I reread point-sections-reconstruction with its exactness and Gamma(B)=R hypotheses, completed-constant-sheaf-reduction for actual flatness and the reduction map, continuous-coefficients-immersion-restriction for Gamma(B)=R, point-proetale-sections-exact, and the DVR statement. The finite quotient identity uses exact sections of multiplication by varpi^n; it does not presume Gamma of an arbitrary quotient commutes without exactness. The actual reconstruction counit, not an arbitrary isomorphism of objects, transfers evaluation. The ordinary Hom-complex node supplies its explicit adjunction and the sign; the completed-evaluation node supplies the integral completed equality. Parent step 3 cites the new node exactly for these conclusions on C=Ra!K; the C hypothesis is supplied by parent step 1. The complete old calculation below remains the future worker's proof assignment.

For the field node I reread base-change-rhom-perfect, coefficient-frobenius, point-scalar-hom-evaluation and point-sections-scalar-extension, including their actual arrow and tower clauses. Perfectness is asserted only for finitely generated integral point complexes over the DVR, and computations use bounded finite-projective models even for torsion cohomology. The map delta is the stated extension of h to h(x)ab, so it preserves the evaluation sign. Localized morphisms require multiplication by their scalar and additivity, not just checking integral maps. The common-stage conclusion uses the actual phi, not an arbitrary point equivalence. Parent step 4 cites the new field statement for the equality and independence that it explicitly states.

For parent step 5 I read thm-pod-global-verdier-duality's source: it constructs g by applying F to the exchange and identifying the source by j. Therefore g = F(e)j inverse is the definition of this specified map; substituting the preceding equations and cancelling inverse isomorphisms proves the final equality and both inverse equations. This uses no pairing or smooth orientation. The canonical-map quotes in citations.json are copied verbatim from the cited statements, with their construction checked against the listed source proofs.

Small-case checks: K=0 gives zero represented objects and the unique inverse identities; a=id_s reduces both counits and the mate to their identity normalization; the coefficient unit and its shifts give the usual signed evaluation. A finite-coefficient torsion module is never assumed projective. Integral R/varpi is represented by the two-term finite-free resolution and rationalizes to zero, so no ordinary dual is incorrectly substituted for the derived dual and the field formula still holds. E=L makes the scalar arrow the identity; E contained in L contained in M gives multiplication of the same scalars in both orders. None of the new statements claims ambient non-torsion small-etale duality or an unrestricted exceptional adjoint.

Checklist B–E: new nodes introduce their objects and coefficient stages, cite their defining notions, have empty proof/proof_deps and null proof_origin, use single-escaped TeX after JSON decoding, and carry exact blueprint provenance. Search verdicts reflect the actual hits. The parent cites only claims in the opened statements, retaining source-defined canonical-map constructions; no cycle through the parent is used in the new statement dependencies. The original arguments are not relabelled as one monolithic lemma; three different reusable assertions take comparable parts, and the exchange and final inverse remain proved in the parent. I checked the new nodes against all relevant near-duplicates above. There is no changed statement and no statement dispute. Every parent step is below 2000 characters, and total proof text is below 3000; no long hidden argument remains in the assembly.

## Complete retained argument and future proof assignments

The following is copied verbatim from the returned proof; it is not a proof field of a new unsplit node. Each cited node was opened and its statement checked against its use as described above. This preserves the old argument at full resolution for the workers assigned the three new nodes.

### Old step 1 — lem-pod-structure-hom-chain-realization

First check the domains of the test-object calculation. The conventions [def-pod-conventions] give separated finite-type $a$, the four coefficient stages and $K\in D^b_{ctf}$. The unit $\Lambda_s$ has Tor amplitude $[0,0]$. The finite-Tor exceptional adjunction [fix-prop-adjunctions](2) puts $C=Ra_!K$ and $\omega=Ra^!\Lambda_s$ in their finite-Tor categories. At finite coefficients [thm-sf-ctf-stability](i)–(iii) puts $L=R\mathcal Hom_X(K,\omega)$, $D=Ra_*L$, $H=R\mathcal Hom_s(C,\Lambda_s)$, $La^*T$ and $K\otimes La^*T$ in these categories for every finite-Tor point test object $T$. Integrally, clause (vii) supplies internal-Hom preservation and $D^b_c=D^b_{ctf}$; [lem-sf-integral-direct-image-constructible] supplies the completed ordinary direct image of $L$. The exceptional adjunction already supplies $C$. Rationalization and common finite fields give the same memberships at the two field stages, using [def-weil-derived-pullback-tensor-hom] and the coefficient-passage clause of stability. For a general finite-Tor $N$ on $s$, the exceptional adjunction puts $Ra^!N$ in $D^b_{ctf}(X,\Lambda)$; internal-Hom preservation puts $L_N=R\mathcal Hom_X(K,Ra^!N)$ and $B_N=R\mathcal Hom_s(C,N)$ in the finite-Tor categories. Ordinary direct-image preservation then puts $A_N=Ra_*L_N$ in $D^b_{ctf}(s,\Lambda)$, using the integral direct-image statement and $D^b_c=D^b_{ctf}$ at the integral stage. The prescribed rationalization and common-stage constructions give these memberships at the field stages. This includes $N=\omega_s$. Thus both represented objects and the tests used below lie in the full finite-Tor point category; no site-perfectness or proper coincidence is required.

Cited statements: def-pod-conventions, fix-prop-adjunctions, thm-sf-ctf-stability, lem-sf-integral-direct-image-constructible, def-weil-derived-pullback-tensor-hom.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-lem-tensor-adjunction.proof.md; Step 1: domains of the Hom chain, with the current all-stage preservation statements.

### Old step 2 — lem-pod-structure-hom-chain-realization

For $N\in D^b_{ctf}(s,\Lambda)$ put $L_N=R\mathcal Hom_X(K,Ra^!N)$, $A_N=Ra_*L_N$ and $B_N=R\mathcal Hom_s(C,N)$. Use [lem-pod-hom-chain-counit-formula] with $(f,M)=(a,K)$. Its $\Phi_T^N$ is precisely the reverse, arrow by arrow, of the Hom chain defining each canonical source construction [lem-sf-tensor-hom, fix-lem-tensor-adjunction]: uncurry, precompose with $P_T^{-1}$, exceptional transpose, curry on $X$, ordinary transpose. Thus $\Phi_T^N(t)=\alpha_Nt$ for $\alpha_N=\operatorname{curry}(p_N)$ with the counit composite $p_N$ specified there. To verify the represented inverse, take $v=(\Phi_{B_N}^N)^{-1}(1_{B_N})$. Then $\alpha_Nv=1$; injectivity of $\Phi_{A_N}^N$ gives $v\alpha_N=1$, since both sides map to $\alpha_N$. Therefore the canonical isomorphisms in both source constructions are this $\alpha_N$. At $N=\Lambda_s$ its formula is exactly the displayed $\alpha_s$ in the statement. Naturality in $N$ from the new lemma gives $\alpha_{N'}A(b)=B(b)\alpha_N$ for $b:N\to N'$, where $A(b)=Ra_*R\mathcal Hom_X(K,Ra^!b)$ and $B(b)=R\mathcal Hom_s(C,b)$.

Cited statements: lem-pod-hom-chain-counit-formula, lem-sf-tensor-hom, fix-lem-tensor-adjunction.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-lem-tensor-adjunction.proof.md; Step 1, compared term by term with sk-thm-sf-tensor-hom/lem-sf-tensor-hom.proof.md Steps 1–2.

### Old step 3 — retained parent assembly

Write $w=\omega_{s,\Lambda}$ and take the identity-adjunction isomorphism $u:w\to\Lambda_s$ of [lem-pod-point-dualizing-complex]. The structure-morphism mate in the exchange is $m=Ra^!u$ by [lem-pod-structure-identity-mate], applied to the exceptional adjunction of $a$ and the identity of $s$. The construction of [fix-cor-verdier-exchange] is the inverse tensor–Hom map at $N=w$, followed by $Ra_*R\mathcal Hom_X(K,m)$, hence is $e=A(u)\alpha_w^{-1}$. Step 2 gives $\alpha_sA(u)=\rho\alpha_w$. Cancelling the two inverse isomorphisms yields $e=\alpha_s^{-1}\rho$. The identity morphism satisfies the exceptional hypothesis by its identity adjunction in the point lemma.

Cited statements: lem-pod-point-dualizing-complex, lem-pod-structure-identity-mate, fix-cor-verdier-exchange.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-cor-verdier-exchange.proof.md; Steps 1–2: compute the structure-morphism mate when a_Y is the identity.

### Old step 4 — lem-pod-point-integral-evaluation-normalization

At finite or integral coefficients put $(R,B)=(A_{E,n},(A_{E,n})_s)$ or $(\mathcal O_E,\widehat{\mathcal O}_{E,s})$ and $L_RM=B\otimes_{\underline R}\underline M$. We verify the hypotheses of [lem-pod-point-sections-reconstruction]. By [lem-weil-l-adic-extension-integers-dvr], $\mathcal O_E$ is a principal ideal domain. Exact sheafification [lem-weil-pbc-site-r-module-presheaf-sheafification-exact] makes $M\mapsto\underline M$ exact; at finite level $L_RM=\underline M$, and integrally $B$ is flat over $\underline{\mathcal O_E}$ by [lem-weil-pbc-completed-constant-sheaf-reduction] (with $A=\mathcal O_E$, $I=(\varpi_E)$), so $L_R$ is exact. Sections are exact by [lem-weil-point-proetale-sections-exact]. Integrally [lem-weil-pbc-continuous-coefficients-immersion-restriction] for $X=s$ gives $\Gamma(s,B)=C(\{*\},\mathcal O_E)=\mathcal O_E$. Multiplication by $\varpi_E^n$ is injective on $\underline{\mathcal O_E}$, hence on the flat $B$, and the reduction isomorphism of [lem-weil-pbc-completed-constant-sheaf-reduction] identifies its cokernel with $(A_{E,n})_s$; exact sections of $0\to B\to B\to(A_{E,n})_s\to0$ give $\Gamma(s,(A_{E,n})_s)=A_{E,n}$ through the constant-value map. By [def-weil-finite-coefficient-point], $c=FC=\Gamma(s,C)$ has bounded finite, resp. finitely generated, cohomology. Hence [lem-pod-point-sections-reconstruction] applies with its explicit adjunction: the unit $c\to\Gamma(s,L_Rc)$ is a quasi-isomorphism, $L_Rc\in D^b_c(s,R)$, integrally $c$ has a bounded finite-projective representative $P$ with $L_RP$ a constructible representative of $L_Rc$, and the actual counit $L_Rc\to C$ is an isomorphism. We henceforth compute on $L_Rc$ (or $L_RP$) through this specified counit, rather than identifying arbitrary point sheaves with modules.

Cited statements: def-weil-finite-coefficient-point, lem-pod-point-sections-reconstruction, lem-weil-l-adic-extension-integers-dvr, lem-weil-pbc-site-r-module-presheaf-sheafification-exact, lem-weil-pbc-completed-constant-sheaf-reduction, lem-weil-point-proetale-sections-exact, lem-weil-pbc-continuous-coefficients-immersion-restriction.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md; Second sentence, expanded by the sections/extension-of-scalars adjunction and the actual counit model.

### Old step 5 — lem-pod-point-integral-evaluation-normalization

At finite coefficients choose a K-flat representative of $c$ with flat terms using [lem-pc-kflat-resolution] on the one-object ringed site $R$. Apply [lem-pod-point-derived-hom-evaluation]; its hypotheses (exact $L_R$ and sections, $\Gamma(s,B)=R$) were verified in Step 4. With a K-injective resolution $B\to I$, the chain isomorphism $h\mapsto(x\mapsto h(1\otimes x))$ computes $FH\to c^\vee$ and preserves derived evaluation. On constructible inputs the tensor comparison is the specified one of [lem-sf-point-fibre-derived-tensor], so this comparison is precisely its evaluation transpose $\kappa$. Integrally the perfect model $P$ of Step 4 meets [lem-pod-point-completed-evaluation]; its displayed equation gives the same conclusion for completed tensor. By the construction of the point-dualizing identification [lem-pod-point-dualizing-complex], $j$ is obtained by applying $R\mathcal Hom_s(C,u)$ and this coefficient-Hom comparison. Thus at both stages $j=\kappa F\rho$ as derived morphisms. Both $j$ and $F\rho$ are isomorphisms, so this specified $\kappa$ is an isomorphism.

Cited statements: lem-pc-kflat-resolution, lem-pod-point-derived-hom-evaluation, lem-sf-point-fibre-derived-tensor, lem-pod-point-completed-evaluation, lem-pod-point-dualizing-complex.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md; Second sentence: explicit Hom-complex comparison and evaluation normalization.

### Old step 6 — lem-pod-point-field-evaluation-normalization

At $E$ choose the integral representative specified by [def-weil-derived-pullback-tensor-hom, def-weil-finite-coefficient-point]. Its evaluated integral complex is perfect by [lem-weil-coefficient-frobenius]; use the bounded finite-projective model $P$ of Step 4. By the construction of [lem-pod-point-dualizing-complex] at $E$, $j$ is the rationalized integral identification followed by the perfect scalar-Hom isomorphism $\delta$ of [lem-pc-base-change-rhom-perfect], the $E$-linear extension of $h\mapsto h\otimes1$, so on representatives $\delta(h\otimes a)=(x\otimes b\mapsto h(x)ab)$. The rational tensor comparison of [lem-sf-point-fibre-derived-tensor] is the balanced map on the same models, so $\kappa$ at $E$ is the transpose of $\Gamma(s,\operatorname{ev})\otimes E$; evaluating $\delta(h\otimes a)$ on $x\otimes b$ gives $h(x)ab$ with the same sign $(-1)^{pj}$, hence $\kappa_E=\delta\circ(\kappa\otimes E)$, while $F\rho$ at $E$ is $F\rho\otimes E$. Tensoring the integral equation of Step 5 with $E$ and composing with $\delta$ gives $j=\kappa F\rho$ at $E$, also when the integral representative has torsion. For a localized morphism $v\otimes a$, naturality is the integral naturality equation multiplied by $a$, and additivity handles sums. At $\overline{\mathbf Q}_\ell$ represent $C$ over a finite field $E$; the equation holds at that stage. For a larger finite field $L$, [lem-pod-point-scalar-hom-evaluation], applied to $P$ and its dual model, identifies the internal-Hom scalar comparison (the transpose of scalar-extended evaluation) through $\varphi$ of [lem-weil-point-sections-scalar-extension] with the coefficient arrow $P^\vee\otimes_RR'\to\operatorname{Hom}^\bullet_{R'}(P\otimes_RR',R')$, after rationalization and compatibly with identities and towers. Thus the representatives of both sides at $E$ and $L$ correspond, and $j=\kappa F\rho$ holds in the common finite-stage category.

Cited statements: def-weil-derived-pullback-tensor-hom, def-weil-finite-coefficient-point, lem-weil-coefficient-frobenius, lem-pod-point-dualizing-complex, lem-pc-base-change-rhom-perfect, lem-sf-point-fibre-derived-tensor, lem-pod-point-scalar-hom-evaluation, lem-weil-point-sections-scalar-extension.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md; Second sentence at E and algebraically closed coefficients: rationalization and common-stage evaluation calculation.

### Old step 7 — retained parent assembly

Finally the global comparison of [thm-pod-global-verdier-duality] is constructed by applying the point functor [def-weil-finite-coefficient-point] to the exchange $e$ and using the specified point-dualizing identification on its source. Spelling out this source construction gives $g=F(e)j^{-1}$. Substituting the equalities of Steps 3 and 5–6 and cancelling inverse isomorphisms gives
$$\begin{aligned}
g&=F(\alpha_s)^{-1}F(\rho)(\kappa F(\rho))^{-1}\\
 &=F(\alpha_s)^{-1}\kappa^{-1}=(\kappa F(\alpha_s))^{-1}.
\end{aligned}$$
Functoriality carries the inverse identities through $F$, and these displayed cancellations prove both inverse equations. All point identifications are the coefficient-stage ones of [lem-pod-point-dualizing-complex]; the integral operations remain completed, and the field calculations are those of Step 6. No smooth orientation, proper-support identification or Poincare pairing enters this calculation.

Cited statements: thm-pod-global-verdier-duality, def-weil-finite-coefficient-point, lem-pod-point-dualizing-complex.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/thm-pod-global-verdier-duality.proof.md; First paragraph: evaluate the exchange and identify its source; substitute the normalization equations.

## Size check

Parent proof text: 2110 characters. New task argument sizes from the retained old proof: 2761, 2864, 1918 characters. Three new nodes, zero Mathlib leaves. All existing item fields outside the stage-1 owned fields are retained.

## Delivery validation

The required deliver.py --no-push invocation exited successfully on 2026-10-22 with `OK (not pushed)` at 02178ab8d44 and `preflight passed`. The checks ran on the server through the delivery tool; no check_dag, review_split or preflight script was run locally, and no compiler or build tool was run. This report update is followed by a final dry run and then direct delivery, as authorized by the worker brief.
