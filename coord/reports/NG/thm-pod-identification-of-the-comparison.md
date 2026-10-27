# Worker report

## Files written

- dag/nodes/sec-six-functors/thm-pod-identification-of-the-comparison.json: parent assembly, statement unchanged.
- dag/nodes/sec-six-functors/lem-pod-comparison-test-adjunctions.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors/lem-pod-smooth-pairing-point-transport.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim quotations for each parent-step citation.

## Attachments

None. I searched lean/WeilConjectures for the item tag, the comparison notion, and projection/counit and trace/cup formulas. The library's CategoryTheory.Verdier.isIso_exchange_of_isIso is a closed abstract isomorphism theorem; it does not state the geometric all-coefficient finite-Tor domain assertions and the five specified bijections of the first new node. CategoryTheory.Verdier.uncurry_poincareMap treats unit-coefficient abstract purity, not site-perfect K and all four coefficient categories with the evaluation-defined point comparison. Neither attaches the item or either complete new statement. No Lean was written or compiled.

## WANTED

None. Both tasks follow the available current blueprint proof, with its cited current DAG statements. No forbidden source route is used.

## Repair and current base

The dispatcher retained only .brief files: no node, report, citations or search log was in this sandbox. I copied the current repository item, whose six-step proof matches the return (including the earlier normalization repairs), into the sandbox and preserved its full text below. This is not an unchanged re-push. Its statement and imported metadata are retained. The new nodes are independent unsplit statements with no proof steps or proof dependencies; their complete intended arguments are preserved below rather than put into their JSON statements. The parent proof is 1802 characters, in three steps. The old reviewed field is inherited metadata certifying the old delivery, not a claim of fresh independent review.

The return has one numbered demand: redistribute all 7296 characters of argument among at least two comparable new statement-only nodes, retaining an assembly under 3000 characters. Old steps 1 and 4 belong to lem-pod-comparison-test-adjunctions (domains and specified Hom chain); old steps 2 and 3 belong to lem-pod-smooth-pairing-point-transport (point comparison, cup/evaluation/trace and smooth identification); old step 5 remains as parent step 2; old step 6 remains as parent step 3. The extracted tasks each contain a separate argument, neither asserts invertibility of the Poincare adjoint or identifies its global inverse. They can be worked on independently.

## Not duplicates

lem-pod-comparison-test-adjunctions vs lem-sf-tensor-hom: the existing node states a canonical internal-Hom exchange isomorphism; the new node supplies all domains at all four stages and the five actual test-object bijections with their counit/projection formulas. It does not restate the exchange-isomorphism conclusion.
lem-pod-comparison-test-adjunctions vs fix-lem-tensor-adjunction: the existing isomorphism statement has no test-object chain, no formulas for its five bijections, and no geometric domain assertion.
lem-pod-comparison-test-adjunctions vs lem-pod-global-duality-map-identification: the latter identifies one exchange map and its canonical inverse; it does not state the intermediate Hom bijections and domain assertions. The new task carries the original independent adjunction-chain argument rather than importing details from that lemma's proof.
lem-pod-comparison-test-adjunctions vs nt-target-poincare-isiso: that node is for condensed algebraically closed coefficients and the unit K; it does not give these four-stage site-perfect-domain bijections.
lem-pod-smooth-pairing-point-transport vs lem-sf-identification-fibre-adjunction: the existing generic point-transport result does not compare the actual cup/evaluation/trace pairing through the geometric smooth orientation; the new node does. Its point-transport portion can reuse that lemma.
lem-pod-smooth-pairing-point-transport vs lem-pod-global-duality-map-identification: the existing lemma explicitly contains no smooth orientation or Poincare pairing; the new task is the geometric factorization through that orientation. Its j=kappa F rho normalization reuses the existing lemma.
lem-pod-smooth-pairing-point-transport vs thm-sf-dual-perfect: that node gives the sheaf dual comparison and evaluation compatibility, not its global cup/trace and point-fibre factorization.
lem-pod-smooth-pairing-point-transport vs nt-target-poincare-uncurry: the existing target concerns condensed Qlb and unit coefficients on a relative base; the new statement is the actual four-stage point pairing for arbitrary site-perfect K.
lem-pod-smooth-pairing-point-transport vs lem-pod-rational-purity-pairing: that node asserts Weil equivariance at the two field stages; the new statement identifies the derived pairing and transpose at all four stages without a Weil structure.

I searched the whole DAG for Hom chain, paired adjunction, projection/counit, pairing/orientation and trace/cup; opened the neighboring statements listed above; ran blueprint_refs ancestor and searches for projection counit, pairing orientation, counit, Poincare pairing, tensor Hom, counit pairing and test objects. No imported node has either complete new statement. The shared blueprint source is a common source, not evidence of duplicate statements.

## Searches read

Each new node records its own first plain-language query, a second phrasing, Loogle, grep and LeanSearch exactly as run by msearch.py. Raw outputs are retained in search-0.txt through search-9.txt and the command's searches.jsonl. I read every hit: A has rigid tensor-Hom equivalences, closed structures and reflective exponential ideals; B has evaluation/currying and cartesian exponential comparison identities, root pairings and simplicial pairings. None gives the geometric four-coefficient assertions. I read Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean at lines 300–370 and Ideal.lean at 235–265: ofEquiv_curry_def/ofEquiv_uncurry_def transport a chosen closed structure, while bijection concerns reflective exponential ideals. Those are tools for portions, not one-line specializations giving either full new node. The source grep was also logged with its exact pattern. No Mathlib leaves claimed. The parent's historical searches are retained as they were; no old search is claimed as a new run.

## Review by NG

I read the item and its main-20261015 statement and complete proof, the sec-six-functors chapter and sk-thm-sf-package unit. This keeps the unit's duality/identification route and uses the purity orientation only through thm-sf-dual-perfect. The original proof's non-elementary ingredients remain in the extracted tasks, with their original citations and source places below. I opened every statement they cite: conventions and perfectness; finite-Tor stability, both integral direct-image constructibility results; the actual ordinary and exceptional adjunctions and their restricted tensor-Hom adjunction; the derived operations and projection definition/formula; the point functor, coherent tensor/unit comparison and point dualizing comparison; coefficient dual, mixed-support cup, normalized Poincare pairing and smooth evaluation-compatible dual comparison; the closed uncurry laws and existing global-duality map-identification and global Verdier-duality theorem.

Parent step 1 uses the first new node for C,D,H and all test-domain assertions and its actual Phi chain, and the second for the invertible kappa/theta and the actual b-sharp factorization. Their statements explicitly give these assertions. Step 2 uses the stated naturality in both inputs of fix-prop-projection-formula, the first new node's explicit formula for Phi_T(t), and the closed uncurry composition identity. Substituting the naturality equation gives precisely the specified pairing; the tests H and D are justified by the first node, and give a two-sided inverse with no cohomology-map detection gap. Step 3 uses the existing global-duality-map-identification's actual alpha_s formula and g=(kappa F alpha_s)^(-1), and the second new node's evaluation-defined kappa and theta. Thus the global map is the specified one, not an arbitrarily chosen isomorphism. citations.json contains verbatim substrings of these current statements.

For the first new node, I checked all five domains: T and C,D,H are bounded ctf on s; La^*T, K tensor La^*T, omega,L are bounded ctf on X. Finite coefficients use stability (i)–(v); integrally stability (vii) gives internal Hom/exceptional preservation and ctf=c, and the two integral constructibility lemmas cover ordinary and compact-support direct images. Rational/common-stage operations are those stipulated in the same conventions, not discrete etale non-torsion operations. No unbounded exceptional adjoint or properness is assumed. The ordinary and exceptional counits are in the stated adjunction nodes, and the second/fifth arrows are the restricted tensor-Hom adjunction with symmetry as required.

For the second new node, I checked the current expanded mixed-support definition in full. Its projection input is Ra_*L=D; the cup is exactly PF followed by Ra_!(1 tensor epsilon_L), evaluated with tau. The definition of the Poincare pairing normalizes the trace as exceptional counit through the same eta_X used by theta. Evaluation compatibility of thm-sf-dual-perfect makes the beta equality an identity of derived morphisms. I wrote the unit comparison u_0:F Lambda_s -> Lambda explicitly, which was implicit in the old step formulas, so p and kappa have the correct codomain. The point normalization j=kappa F rho is supplied by the actual statement of lem-pod-global-duality-map-identification, not inferred from the mere existence of an isomorphism in point-dualizing-complex. The rho inverse and naturality of tau then give the point transpose formula for all v.

Small cases: K=0 gives zero objects and the unique maps, for which all bijections and factorizations hold. X=s,d=0 gives the identity counit and the ordinary closed evaluation. At n=1 no freeness or self-injectivity inference is used. For nonproper X=A^1, compact support remains the first input and ordinary cohomology the second, and the formulas never identify Ra_! with Ra_*. Integral torsion is allowed because the whole assertion stays derived; no false degreewise perfectness claim appears. Nonzero shifts of K are handled by the given derived evaluation conventions, with K always the left factor. No statement dispute was found.

B–E checks: each node is self-contained and statement-only, all bracketed notions have stmt_deps, TeX is singly escaped in the decoded JSON, and the source is a precise blueprint place (no unsupported Stacks tag or forbidden source added). Every non-elementary parent use is cited by its statement; no cycle is introduced, since neither new node depends on the parent. No parent step exceeds 2000 characters; no new proof steps exist. Neither new node asserts the parent or a parent clause. The original argument texts below retain all details rather than replacing them by labels.

## Unfinished work

Only the intended unsplit proofs of the two new nodes remain for parallel stage-1 workers. This delivery completes the requested one-level split; no Lean work is authorized.

## Preserved arguments for new workers

### lem-pod-comparison-test-adjunctions

Original step 1:

Work in [def-pod-conventions] at the fixed coefficient stage. Thus $a=a_X:X\to s$ is separated finite type and admissible, $X$ is smooth of pure dimension $d$, and $K$ is bounded constructible finite-Tor and site-perfect [def-pod-perfect-complex-on-x]. Put
$$C=Ra_!K,\quad \omega=Ra^!\Lambda_s,\quad L=R\mathcal Hom_X(K,\omega),\quad D=Ra_*L,\quad H=R\mathcal Hom_s(C,\Lambda_s).$$
These objects belong to their bounded constructible finite-Tor categories. At finite coefficients apply exceptional preservation, internal-Hom preservation, and both direct-image assertions of [thm-sf-ctf-stability]. Integrally use its clause (vii) for internal Hom, exceptional preservation and $D^b_c=D^b_{ctf}$, and [lem-sf-integral-direct-image-constructible] and [lem-sf-integral-compact-support-constructible] for $D$ and $C$. The same clause and the coefficient-passage constructions give the field stages. In particular the projection formula may be applied with second input $D$, and the exceptional counit is defined at $\Lambda_s$.

Cited statements: def-pod-conventions, def-pod-perfect-complex-on-x, thm-sf-ctf-stability, lem-sf-integral-direct-image-constructible, lem-sf-integral-compact-support-constructible. Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/thm-pod-identification-of-the-comparison.proof.md, first paragraph: geometry and domains.

Original step 4:

Take an arbitrary $T\in D^b_{ctf}(s,\Lambda)$, not just a shift of the unit. By [thm-sf-ctf-stability], $La^*T$ and $K\otimes^L_{\Lambda_X}La^*T$ lie in $D^b_{ctf}(X,\Lambda)$, so the projection formula applies to $(K,T)$ and the exceptional adjunction applies to its tensor product and $\Lambda$. The ordinary and exceptional adjunctions at all four coefficient stages are [fix-prop-adjunctions] (1), (2), with the exceptional functor of [def-weil-exceptional-inverse-image]. The restricted tensor–internal-Hom adjunction is [det-thm-sf-ctf-stability-adjunctions] (2), with the symmetry interchanging the tensor factors when needed. The operations are those of [def-weil-derived-pullback-tensor-hom]. Thus the adjunctions and the projection isomorphism [def-exchange-projection], [fix-prop-projection-formula] give a natural bijection $\Phi_T$:
$$
\begin{aligned}
\operatorname{Hom}_s(T,D)
&\cong\operatorname{Hom}_X(La^*T,L)\\
&\cong\operatorname{Hom}_X(K\otimes^L_{\Lambda_X}La^*T,Ra^!\Lambda)\\
&\cong\operatorname{Hom}_s(Ra_!(K\otimes^L_{\Lambda_X}La^*T),\Lambda)\\
&\cong\operatorname{Hom}_s(C\otimes^L_\Lambda T,\Lambda)\\
&\cong\operatorname{Hom}_s(T,H).
\end{aligned}
$$
The first bijection sends $t$ to $\varepsilon_L\circ La^*t$, where $\varepsilon$ is the ordinary counit. The next sends it to evaluation against $K$, the third sends $e$ to $\mu\circ Ra_!e$, and the fourth precomposes with $P_T=\operatorname{PF}_{a,K,T}:C\otimes T\xrightarrow{\sim}Ra_!(K\otimes La^*T)$. The fifth curries, with evaluation and transpose laws [lem-pod-closed-uncurry-laws]. These are natural bijections on every test object in the stated category; no adjunction for ordinary uncompleted integral operations has been substituted for the completed one.

Cited statements: thm-sf-ctf-stability, fix-prop-adjunctions, def-weil-exceptional-inverse-image, det-thm-sf-ctf-stability-adjunctions, def-weil-derived-pullback-tensor-hom, def-exchange-projection, fix-prop-projection-formula, lem-pod-closed-uncurry-laws. Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/thm-pod-identification-of-the-comparison.proof.md, second paragraph and displayed Hom chain.

### lem-pod-smooth-pairing-point-transport

Original step 2:

Write $F=\operatorname{Fib}_s$ [def-weil-finite-coefficient-point], $c=FC$, and $h=R\operatorname{Hom}_\Lambda(c,\Lambda)$. Use the tensor/unit comparison $\tau_{M,N}:F(M\otimes N)\xrightarrow{\sim}FM\otimes FN$ of [lem-sf-point-fibre-derived-tensor]. The evaluation-defined comparison
$$\kappa:FH\longrightarrow h$$
is precisely the specified map in [lem-pod-global-duality-map-identification]. That statement gives $j=\kappa F\rho$, where $j:F(D_sC)\to h$ is the isomorphism of [lem-pod-point-dualizing-complex] and $\rho=R\mathcal Hom_s(C,u)$ for the identity-adjunction isomorphism $u:\omega_s\to\Lambda_s$. Hence $\rho$ is invertible, with inverse $R\mathcal Hom_s(C,u^{-1})$, and $\kappa=j(F\rho)^{-1}$ is invertible. By its definition as the transpose of transported evaluation,
$$\operatorname{ev}^{\mathrm{coeff}}(1_c\otimes\kappa)=F(\operatorname{ev}_{C,\Lambda_s})\tau_{C,H}^{-1}.$$
Consequently, for any $v:V\to H$, the coefficient transpose of $F(\operatorname{ev}_{C,\Lambda_s}(1_C\otimes v))\tau_{C,V}^{-1}$ is $\kappa Fv$: substitute the displayed identity and naturality of $\tau$, then apply the inverse transpose laws [lem-pod-closed-uncurry-laws]. This uses the existing normalization lemma for the point internal-Hom comparison, rather than reproving that comparison on shifted-unit tests.

Cited statements: def-weil-finite-coefficient-point, lem-sf-point-fibre-derived-tensor, lem-pod-global-duality-map-identification, lem-pod-point-dualizing-complex, lem-pod-closed-uncurry-laws. Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/thm-pod-identification-of-the-comparison.proof.md, first paragraph: evaluated internal-Hom comparison.

Original step 3:

Let $\varepsilon_L:La^*D\to L$ and $\mu:Ra_!\omega\to\Lambda_s$ be the counits [fix-prop-adjunctions], and write $P_T=\operatorname{PF}_{a,K,T}$ [fix-prop-projection-formula]. Define the sheaf pairing and its coefficient version by
$$e=\operatorname{ev}_{K,\omega}(1_K\otimes\varepsilon_L),\qquad p_s=\mu\,Ra_!e\,P_D,\qquad p=Fp_s\,\tau_{C,D}^{-1}.$$
This is exactly the mixed-support cup product followed by evaluation and the exceptional counit: [def-pod-mixed-support-cup-product] specifies the projection input $Ra_*L=D$ and then the ordinary counit, evaluated by $F$ with this tensor comparison. The evaluation-compatible smooth comparison of [thm-sf-dual-perfect] gives
$$\theta:FD\xrightarrow{\sim}Q=R\Gamma(X,K^\vee(d))[2d].$$
The coefficient evaluation [def-pod-coefficient-dual-on-x] and the all-stage trace normalization in [def-pod-derived-poincare-pairing] give
$$\beta_K=p(1_c\otimes\theta^{-1}).$$
Indeed the latter trace is the exceptional counit through the same orientation used by $\theta$; evaluation compatibility and naturality of the cup construction identify every preceding arrow. Put $b_s=\operatorname{curry}(p_s):D\to H$. Step 2 and [lem-pod-closed-uncurry-laws] now give
$$b_K^\sharp=\kappa Fb_s\,\theta^{-1}.$$
No higher-coefficient trace assertion is taken from a finite-only trace node.

Cited statements: fix-prop-adjunctions, fix-prop-projection-formula, def-pod-mixed-support-cup-product, thm-sf-dual-perfect, def-pod-coefficient-dual-on-x, def-pod-derived-poincare-pairing, lem-pod-closed-uncurry-laws. Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/thm-pod-identification-of-the-comparison.proof.md, first paragraph: actual pairing and smooth comparison.

For the transport worker: insert u_0 after every F-valued pairing as in the new statement. The equality j=kappa F rho is the existing normalization lemma, and the canonical evaluation identity follows by the definition of kappa. For the test-adjunction worker: retain the arbitrary-T formulation, not only shifted-unit tests.

### Parent calculations retained

Original step 5:

In the Hom bijection $\Phi_T$ just constructed, let $t:T\to D$ and put $e_t=e(1_K\otimes La^*t)$. Naturality of [fix-prop-projection-formula] gives
$$P_D(1_C\otimes t)=Ra_!(1_K\otimes La^*t)P_T.$$
Thus the uncurried value of the Hom chain is
$$\mu Ra_!e_t P_T=\mu Ra_!e P_D(1_C\otimes t)=p_s(1_C\otimes t).$$
The transpose laws [lem-pod-closed-uncurry-laws] give $\Phi_T(t)=b_s t$. This explicitly identifies the morphism represented by the adjunction chain with the specified pairing, rather than only identifying its source and target. Take $T=H$ and $v=\Phi_H^{-1}(1_H)$. Then $b_s v=1_H$. At $T=D$, injectivity of $\Phi_D$ gives $v b_s=1_D$, since
$$\Phi_D(vb_s)=b_svb_s=b_s=\Phi_D(1_D).$$
Both tests are allowed by Step 1. Hence $b_s$ is an isomorphism, and so is $b_K^\sharp=\kappa Fb_s\theta^{-1}$. This is a two-sided inverse argument on actual morphisms; equality of cohomology maps is not used to identify derived maps.

Original step 6:

Apply [lem-pod-global-duality-map-identification] with these $a,K,C,\omega,L,D,H$ and the comparison $\kappa$ fixed in Step 2. Its formula
$$\alpha_s=\operatorname{curry}\bigl(\mu Ra_!(\operatorname{ev}_{K,\omega}(1_K\otimes\varepsilon_L))P_D\bigr)$$
is exactly $b_s$, by the definition in Step 3. The lemma states, for the actual canonical global Verdier-duality map $g:c^\vee\to FD$, that
$$g=(\kappa F\alpha_s)^{-1}=(\kappa Fb_s)^{-1}.$$
The global map here is the one of [thm-pod-global-verdier-duality], not an independently chosen isomorphism. Therefore
$$(\theta g)b_K^\sharp=\theta g\kappa Fb_s\theta^{-1}=1_Q,\qquad b_K^\sharp(\theta g)=\kappa Fb_sg=1_{c^\vee}.$$
Its inverse is global Verdier duality followed by the smooth comparison $\theta$ of [thm-sf-dual-perfect], as claimed. The normalization and point-comparison argument formerly hidden in the long final step is now an explicit citation of the existing lemma's statement. Properness is used nowhere.

