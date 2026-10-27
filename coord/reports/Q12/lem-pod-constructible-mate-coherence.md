# Q12 repair: lem-pod-constructible-mate-coherence

## Files written

- dag/nodes/sec-poincare-duality/lem-pod-constructible-mate-coherence.json: statement unchanged; 15 long steps replaced by six assembly steps (2483 characters).
- dag/nodes/sec-poincare-duality/lem-pod-equivariant-mates-coefficient-transport.json: statement, unsplit, no Mathlib match; no proof steps and no proof dependencies.
- dag/nodes/sec-poincare-duality/lem-pod-frobenius-evaluation-projection-coherence.json: statement, unsplit, no Mathlib match; no proof steps and no proof dependencies.
- dag/nodes/sec-poincare-duality/lem-pod-frobenius-pullback-monoidal-adjunction-coherence.json: statement, unsplit, no Mathlib match; no proof steps and no proof dependencies.
- dag/nodes/sec-poincare-duality/lem-pod-semilinear-exchange-cube-coherence.json: statement, unsplit, no Mathlib match; no proof steps and no proof dependencies.

The four new tasks have statement lengths 2904, 3434, 3836 and 2872 characters (including their self-contained hypotheses). They divide the substantive comparison arguments; none restates the whole item. Generic invertible-mate and adjunction-lifting results already exist and are reused. citations.json contains a verbatim statement excerpt for every cited node at every parent step. returned-proof.json preserves the returned live node; the complete original argument is also retained below, since new unsplit nodes must contain statements rather than proof sketches.

## Attachments

None. The exact item tag is absent from WeilConjectures. The existing CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction and its carrier-unit/counit lemmas cover the generic lemma already represented by lem-sf-fixed-pair-adjunction-lift; they do not state the rational/common-stage scheme comparison clauses of this item. UpperShriekComposition supplies constructible composition mate results, not all of these Frobenius operation, tensor, projection and coefficient assertions. The actual derived Weil operations in WeilSheaf/Operations, LowerShriekOperations and DerivedHom use different category models and do not attach the item or the new conjunctions.

## WANTED

None newly required. The new statements extract the explicit agent-written argument already accepted into this node. They follow the current blueprint rather than claiming that a human-written reference proves each extracted assertion.

## What was wrong / repair of the return

The returned node had 12019 characters of argument in 15 steps. The human's re-split decision requires independent work packages, not an abridged proof. Its statement was retained byte for byte. Its proof is now a short assembly of existing categorical results and four new statement-only nodes. No axioms, extra exceptional-admissibility assumption, separatedness of X_0 or Y_0, invariant integral lattice or enlargement of comparison domains was added.

The sandbox originally contained only dispatcher marker files, not the announced prior delivery. The first required dry run exited with “no node files”. I therefore copied the current live returned node, including its proof, searches, blueprint and maintainer fields, and preserved it in returned-proof.json. I did not run git or change the shared repository. No other attempt's files existed to retain. The current node is the same 15-step version described by the return.

## Argument allocation

1. Old steps 1–2: parent step 1 reuses the already existing compact-support Frobenius exchange and equivalence-mate lemma, with the same coefficient/domain restrictions and substitution (L=L'=F, R=R'=G, non-adjoint sides S,T, square a^{-1}).
2. Old steps 3–6: parent step 2 retains the two explicit mate equations and uses the existing fixed-pair adjunction theorem for functoriality, unit/counit equivariance, restricted Hom bijections and triangles. These arguments were not copied into a duplicate new node.
3. Old step 7: the equation test for comparisons is explicitly in the new pullback/monoidal and exchange statements; parent step 5 retains composition, inversion and lifted-functor whiskering. The mate/coefficient node records the consequent inverse-reflection clause on the given domain.
4. Old steps 8–9: new lem-pod-frobenius-pullback-monoidal-adjunction-coherence states the exact Ex_* mate normalization, both ordinary unit/counit equations and lifted adjunction, pullback composition equation and all tensor coherence equations. This is one comparison-calculus task; no exceptional-admissibility clause is used.
5. Old steps 10–11: new lem-pod-semilinear-exchange-cube-coherence states the relabeling identification, the actual exchange-cube and direct-image composition equations and the refinement equation. It has both ordinary and compact-support versions on the prescribed coefficient domains.
6. Old steps 12–13: new lem-pod-frobenius-evaluation-projection-coherence states the full evaluation identity, the actual counit-defined ordinary projection, the open comparison square including the inserted beta and mu maps, its strict-system version and supplied realizations, and the compactification projection. It assumes the previously proved ordinary and tensor equivariance, allowing an independent proof of this distinct support/evaluation argument.
7. Old steps 14–15: new lem-pod-equivariant-mates-coefficient-transport states the actual three-factor lifted mate, all three types of pasting, rationalization and conjugation under finite coefficient extension, representative independence and the limitation on invertibility. Its hypotheses are abstract lifted adjunctions plus the specified compatible coefficient comparisons, rather than the entire conclusion of the parent.

## Review by Q12

I read the current main-20261015 prop-weil-operations.proof.md in full, especially sentence 1, and the current lem-fix-weil-operations.proof.md: ordinary direct image uses Ex_*, exceptional transport takes the mate of Ex_!, evaluation is natural in the two Weil maps (one inverse), and comparisons use exchange pasting and the tensor/counit projection composite. I also read the unit and chapter records: this is an extraction below sentence 1, not a change to the finiteness or purity route. There is no geometric orientation or trace assertion in a new task and no prohibited SGA route. The precise extracted statements and their proof plans are the returned explicit argument copied below, not a claim that the short blueprint supplies all details.

For the first new node I checked old steps 8–9 against fix-prop-adjunctions(1), the Ex_* transpose in def-exchange-projection, integral pullback associativity in lem-pod-integral-pullback-composition, and naturality/composition/associativity/symmetry/unit in lem-pur-derived-pullback-tensor-iso. I kept only the ordinary adjunction and wrote its two equations. Its self-contained field and pair conventions do not assume X_0,Y_0 separated. The formula is typed with L:Y→X and R:X→Y, so the source Frobenius is P_Y for the unit and P_X for the counit.

For the second new node I checked fix-lem-exchanges(1),(2),(4): it explicitly states naturality, horizontal and vertical pasting with the canonical composition comparisons, and independence/intertwining under compactification refinement. Its square requires separated finite-type arrows and finite-type k-schemes, not separated structural maps. The extracted relabeling has structural map a_W g_W at the source of g_W; g_W then is a k-isomorphism to the original corner and r g_W=g_V r makes r linear between relabeled corners. I retained the restrictions on coefficient stages, origin witnesses and finite Tor, and did not assert invertibility of arbitrary Ex_*.

For the third new node I checked the evaluation convention against sk-def-sf-operations(i) and lem-pod-derived-automorphism-hom-evaluation: evaluation starts at M tensor H(M,N), and its transport identity uses mu followed by 1 tensor h. Evaluation naturality uses H(theta_M^{-1},theta_N), so the variance is correct. For projection I opened def-exchange-projection and lem-sf-open-tensor-normalization: the former defines pi by unit–tensor/counit and PF by Rp_*(gamma) pi; the latter asserts invertible open units, full faithfulness of j_!, the restricted identity normalization of beta/gamma, and the strict inverse-system version. I made the open square explicit: both paths start at Lt^*(j_!M tensor N) and end at j'_!(Ls^*M tensor j'^*Lt^*N), after pullback composition. The source as well as target is supported on the new open (beta and gamma' give the source identification), which is needed to reflect the restricted equality. The old proof's actual support argument is preserved below. I did not infer perfectness of arbitrary constructible objects or equality of derived maps merely from separate finite reductions.

For the fourth new node I checked the exact component formula and transpose bijection in def-weil-pbc-adjunction-mate and all three pasting clauses in lem-weil-pbc-mate-pasting, including changing adjunctions by conjugation. The coefficient hypotheses are explicitly the supplied intertwining of units, counits and comparisons from def-exchange-projection, together with identity/tower cocycles; the new statement proves transport of mates and pasted composites from these hypotheses. The localization/common-stage definitions in def-weil-derived-pullback-tensor-hom apply to arbitrary localized Hom classes, and the intermediate comparison and its inverse cancel under composition. This is not a demand to choose a stable lattice for a Weil structure.

For each parent citation I opened the cited node's statement, rather than borrowing a fact from its proof. Parent step 1 uses exactly the Frobenius compact-support isomorphism (including non-separated bases) and the invertible-mate theorem with S an equivalence and T fully faithful. Parent step 2 uses the displayed unit-mate equation and the mate transpose to obtain the two equations, then the existing fixed-pair adjunction theorem, whose statement supplies both lifts, the original unit and counit and the adjunction. Parent step 3 uses the explicit ordinary/monoidal and exchange identities in the first two new statements; multiplying by the input theta and using naturality is the only assembly argument. Parent step 4 uses the third statement's displayed evaluation and projection assertions, with step 3 discharging its ordinary/tensor equivariance hypotheses. Parent step 5 is only the three written morphism-equation manipulations from the definition of a pair; no uncited categorical theorem is hidden. Parent step 6 uses the fourth statement's actual mate, pasting and coefficient assertions, with the lifted exceptional adjunction and comparisons supplied in previous steps. Its inverse conclusion concerns only comparisons whose carrier is already invertible. Every use has a verbatim quote in citations.json. Each parent step is below 2000 characters and their sum is below 3000.

I tested the new assertions on identity functors/morphisms, the empty scheme, a point with arbitrary invertible rational theta, identity coefficient extension and two successive coefficient extensions. For a point, evaluation reduces to ev(theta_M tensor Hom(theta_M^{-1},theta_N))=theta_N ev. For the identity open immersion beta and gamma become identities, so the open square becomes tensor functoriality. For non-separated bases the only separatedness used is that of the diagram arrows; relabeling changes no underlying morphism. Arbitrary scalar Weil structures on a point need not preserve an integral lattice, so I kept all calculations in the rational/common-stage Hom groups. Noninvertible ordinary exchanges remain noninvertible in the statements; mate or projection equivariance is not used as an invertibility theorem.

Against delivery-errors B–E: all four new nodes are self-contained statements with explicit objects, coefficient stages and domains, empty proof/proof_deps and genuine logged searches; their blueprint via chain is item→prop-weil-operations. I ruled out duplicate generic fixed-pair adjunction and Hom transport nodes by reusing them, and compared the relevant broad blueprint nodes as recorded below. No Stacks numbered lemma is quoted as an unsupported assertion; the sources here are the current blueprint and the already explicit returned categorical argument. Mathlib search hits provide generic mates, ordinary module-sheaf operations or monoidal laws, not these constructible Frobenius and supplied coefficient comparisons. LeanSearch rate-limit failures are recorded unavailable. There is no new-node cycle: none cites the parent and none cites any new node. The parent assembles them in dependency order. No statement change or unresolved mathematical dispute was found.

## Not duplicates

lem-pod-equivariant-mates-coefficient-transport vs lem-pod-constructible-mate-coherence: extracts only the argument allocated above; the parent also constructs the exceptional lift and assembles all operation comparisons, while this task has its own objects and comparison hypotheses.

lem-pod-equivariant-mates-coefficient-transport vs lem-fix-weil-operations: that blueprint statement bundles operations with an admissible exceptional adjoint; this task states the explicit smaller comparison equations and/or coefficient transport on the supplied domains and includes non-separated structural bases. It does not reintroduce exceptional admissibility.

lem-pod-equivariant-mates-coefficient-transport vs prop-weil-operations: the source's umbrella theorem also treats truncations, purity/trace and duality; this task is a strict subsidiary comparison argument under sentence 1.

lem-pod-frobenius-evaluation-projection-coherence vs lem-pod-constructible-mate-coherence: extracts only the argument allocated above; the parent also constructs the exceptional lift and assembles all operation comparisons, while this task has its own objects and comparison hypotheses.

lem-pod-frobenius-evaluation-projection-coherence vs lem-fix-weil-operations: that blueprint statement bundles operations with an admissible exceptional adjoint; this task states the explicit smaller comparison equations and/or coefficient transport on the supplied domains and includes non-separated structural bases. It does not reintroduce exceptional admissibility.

lem-pod-frobenius-evaluation-projection-coherence vs prop-weil-operations: the source's umbrella theorem also treats truncations, purity/trace and duality; this task is a strict subsidiary comparison argument under sentence 1.

lem-pod-frobenius-pullback-monoidal-adjunction-coherence vs lem-pod-constructible-mate-coherence: extracts only the argument allocated above; the parent also constructs the exceptional lift and assembles all operation comparisons, while this task has its own objects and comparison hypotheses.

lem-pod-frobenius-pullback-monoidal-adjunction-coherence vs lem-fix-weil-operations: that blueprint statement bundles operations with an admissible exceptional adjoint; this task states the explicit smaller comparison equations and/or coefficient transport on the supplied domains and includes non-separated structural bases. It does not reintroduce exceptional admissibility.

lem-pod-frobenius-pullback-monoidal-adjunction-coherence vs prop-weil-operations: the source's umbrella theorem also treats truncations, purity/trace and duality; this task is a strict subsidiary comparison argument under sentence 1.

lem-pod-semilinear-exchange-cube-coherence vs lem-pod-constructible-mate-coherence: extracts only the argument allocated above; the parent also constructs the exceptional lift and assembles all operation comparisons, while this task has its own objects and comparison hypotheses.

lem-pod-semilinear-exchange-cube-coherence vs lem-fix-weil-operations: that blueprint statement bundles operations with an admissible exceptional adjoint; this task states the explicit smaller comparison equations and/or coefficient transport on the supplied domains and includes non-separated structural bases. It does not reintroduce exceptional admissibility.

lem-pod-semilinear-exchange-cube-coherence vs prop-weil-operations: the source's umbrella theorem also treats truncations, purity/trace and duality; this task is a strict subsidiary comparison argument under sentence 1.

lem-pod-frobenius-pullback-monoidal-adjunction-coherence vs lem-sf-fixed-pair-adjunction-lift: the existing generic theorem is reused in the parent; the new task identifies the actual Ex_* normalization and pullback/monoidal comparisons in the geometric coefficient categories. It does not create another abstract adjunction-lifting node.

lem-pod-semilinear-exchange-cube-coherence vs fix-lem-exchanges: the existing result states exchange identity/pasting and refinement compatibility in k-linear diagrams; the new task states the semilinear relabeling and the resulting Frobenius-intertwining cube equations for compositions and exchanges.

lem-pod-frobenius-evaluation-projection-coherence vs lem-pod-derived-automorphism-hom-evaluation: the latter supplies the nonequivariant evaluation-characterized transport; the new task inserts arbitrary Weil structures and proves the support-normalized open/projection square. It does not assert a new Hom transport existence theorem.

lem-pod-frobenius-evaluation-projection-coherence vs lem-sf-derived-weil-compact-projection-formula: that theorem concerns actual derived Weil categories on separated schemes; the new task concerns pair categories in the rational/common-stage model, non-separated bases, and the explicit canonical map equations.

lem-pod-equivariant-mates-coefficient-transport vs lem-weil-pbc-mate-pasting: the latter gives carrier categorical pasting formulas; the new task lifts them to fixed pairs and compares their actual localized/common-stage coefficient images.

lem-pod-equivariant-mates-coefficient-transport vs lem-pur-weil-coefficient-diagram-identifications: that statement concerns smooth purity/Tate sources and trace reconstruction with separated bases; this task is formal in supplied lifted adjunctions and arbitrary equivariant square maps, with no smoothness or purity assertion.

No new node cites a Stacks tag. The only identical source-document pairs are the sentence-1 decomposition family; the comparisons above explain the extracted tasks versus the parent and blueprint umbrella statement. The other same-document nodes address purity, truncation, basic operation lifts, duality or canonical source realization, not these comparison equations.

## Searches and source audit

I searched the whole DAG by keywords (equivariant adjunction, fixed pairs, projection/Frobenius, semilinear relabeling, evaluation and mates), and read the close candidate statements. tools/blueprint_refs.py searches included “Weil adjunction”, “Frobenius”, “evaluation projection”, “projection transformation”, “mate”, “evaluation”, “semilinear”, “coefficient”, “tensor evaluation”, “common-stage” and “pullback composition”. The ancestor command gives prop-weil-operations; all new via lists contain the parent item. No exact blueprint match was found for the complete new task statements.

Each new node records two distinct LeanFinder phrasings, a Loogle pattern, a source grep and a LeanSearch attempt, all copied from the command log searches.jsonl. I read the returned candidates. In particular Mathlib CategoryTheory/Adjunction/Mates.lean lines 84–145, 170 onward and 486 onward supplies the generic mate and normalization/pasting formulas already represented by existing nodes; it does not include the additional fixed-pair and common coefficient-stage assertions. Mathlib Endofunctor/Algebra.lean defines algebra carriers/morphisms, not these geometric comparisons. The LeanFinder module-sheaf pullback/pushforward candidates concern ordinary structure-sheaf modules and not completed, scalar-localized or common-stage constant-coefficient constructible categories. These are therefore not one-line specializations. No search has been invented or silently marked successful when unavailable.

## Complete retained returned argument

The following is copied verbatim from every old step, in order. It is the proof plan for the extracted unsplit nodes and the reused generic results. Its placement in the report keeps unsplit node files statement-only and prevents any argument from being lost in the extraction.

### Returned step 1

Work in the specified rational or common-stage categories themselves. The assumed adjunction is the constructible $F\dashv G$ of [def-weil-exceptional-inverse-image]; its unit and counit therefore have exactly these categories as domain. The given $S,T$ are equivalences. Independently, [lem-pod-weil-frobenius-compact-support-exchange] states that the specified $a=\operatorname{Ex}_!:TF\to FS$ is a natural isomorphism on the supplied domains, including the rational/common-stage categories and non-separated $X_0,Y_0$. Thus the last assertion about this particular exchange is already available. Keep its coefficient and finite-Tor domain restrictions throughout. No ambient exceptional adjoint is used.

Uses: def-weil-exceptional-inverse-image, lem-pod-weil-frobenius-compact-support-exchange.

### Returned step 2

Apply [def-weil-pbc-adjunction-mate] with both adjunctions equal to $F\dashv G$, the non-adjoint sides $S,T$, and square $\alpha=a^{-1}:FS\to TF$. Its displayed component formula is precisely $b_L=GT(\varepsilon_L)\,G(a^{-1}_{GL})\,\eta_{SGL}$. In [lem-weil-mate-iso-along-equivalences] take $L=L'=F$, $R=R'=G$, $G_{\rm there}=S$, $G'_{\rm there}=T$, and $\theta=a^{-1}$. The first side is an equivalence and the second is fully faithful because $T$ is an equivalence. That theorem makes this same $b:SG\to GT$ a natural isomorphism. This uses the equivalence hypotheses, not a general assertion that square mates preserve isomorphisms.

Uses: def-weil-pbc-adjunction-mate, lem-weil-mate-iso-along-equivalences.

### Returned step 3

The unit identity of [lem-pur-mate-unit-compatibility], with $\alpha=a^{-1}$, gives $b_{FK}S(\eta_K)=G(a_K^{-1})\eta_{SK}$. Postcompose with $G(a_K)$ to obtain $G(a_K)b_{FK}S(\eta_K)=\eta_{SK}$. The transpose characterization in [def-weil-pbc-adjunction-mate] gives $\varepsilon_{TL}F(b_L)=T(\varepsilon_L)a^{-1}_{GL}$. Precompose with $a_{GL}$ to obtain $\varepsilon_{TL}F(b_L)a_{GL}=T(\varepsilon_L)$. These are the two asserted mate equations, with every component typed in the constructible categories.

Uses: lem-pur-mate-unit-compatibility, def-weil-pbc-adjunction-mate.

### Returned step 4

Set $\theta_{GL}=G(\theta_L)b_L$, an isomorphism since both factors are isomorphisms. For a Weil arrow $u:L\to L'$, naturality of $b$ and the equation $u\theta_L=\theta_{L'}T(u)$ give
$$G(u)G(\theta_L)b_L=G(\theta_{L'})G(Tu)b_L=G(\theta_{L'})b_{L'}S(G(u)).$$
Thus $G(u)$ is a Weil arrow. Its identity and composition laws are the ones of the same underlying $G$. The analogous computation with naturality of $a$ gives the stated lift $\theta_{FK}=F(\theta_K)a_K$. These are actual functors on the categories of pairs in [def-weil-weil-sheaf-complex].

Uses: def-weil-weil-sheaf-complex.

### Returned step 5

For $K$ on $X$, the structure of $GFK$ is $GF(\theta_K)G(a_K)b_{FK}$. By Step 3 and naturality of $\eta$,
$$\theta_{GFK}S(\eta_K)=GF(\theta_K)\eta_{SK}=\eta_K\theta_K.$$
For $L$ on $Y$, the structure of $FGL$ is $FG(\theta_L)F(b_L)a_{GL}$. Naturality of $\varepsilon$ and Step 3 give
$$\varepsilon_L\theta_{FGL}=\theta_L\varepsilon_{TL}F(b_L)a_{GL}=\theta_LT(\varepsilon_L).$$
Consequently the original unit and counit are Weil morphisms, with no replacement of their underlying maps.

Uses: def-weil-weil-sheaf-complex.

### Returned step 6

The two triangle equations are the original equations of the assumed $F\dashv G$ and still hold after forgetting. They hold as equations of Weil morphisms as well, since the forgetful functor of [def-weil-weil-sheaf-complex] is faithful. Explicitly a Weil map $h:FK\to L$ has transpose $G(h)\eta_K$, which is Weil by Steps 4–5; a Weil map $v:K\to GL$ has inverse transpose $\varepsilon_LF(v)$, also Weil. These restrictions of the original Hom bijections are inverse by the triangles. This supplies the lifted adjunction, including naturality, rather than just equivariant functors.

Uses: def-weil-weil-sheaf-complex.

### Returned step 7

We will use the following elementary equation test. If $H,J$ have Frobenius comparisons $c_H:PH\to HQ$, $c_J:PJ\to JQ$, a natural transformation $d:H\to J$ induces a map of pairs whenever
$$d_{QK}c_{H,K}=c_{J,K}P(d_K).$$
Indeed multiply this equality on the left by $J(\theta_K)$ and use naturality $d_KH(\theta_K)=J(\theta_K)d_{QK}$. For Weil arrows $u,v$, $(vu)\theta=v\theta'P(u)=\theta''P(vu)$. If $u$ is invertible, multiplying $u\theta=\theta'P(u)$ by the inverses gives $u^{-1}\theta'=\theta P(u^{-1})$. Applying a lifted functor sends the equation for $u$ to the equation for its image, by naturality of that functor's comparison. Thus composition, both whiskerings by lifted functors, and inverses preserve equivariance; the forgetful functor reflects isomorphisms.

Uses: def-weil-weil-sheaf-complex.

### Returned step 8

For ordinary adjunctions put $L=Lf^*$, $R=Rf_*$. Use only the constructible domains of the ordinary adjunction in [fix-prop-adjunctions](1). The comparison $P_XL\simeq LP_Y$ is pullback composition in the Frobenius square. By the explicit definition of $\operatorname{Ex}_*$ in [def-exchange-projection], the mate of its inverse is exactly the standard comparison $P_YR\to RP_X$: its transpose is the pullback square followed by the ordinary counit. Consequently the calculations in Steps 3–6, replacing $(F,G,S,T)$ by $(L,R,P_Y,P_X)$, prove equivariance of both ordinary adjunction maps for the specified standard lifts. No exceptional-admissibility clause of [fix-prop-adjunctions] is invoked.

Uses: fix-prop-adjunctions, def-exchange-projection.

### Returned step 9

For pullbacks along composable morphisms, expand the Frobenius comparison using the pullback-composition maps. The two maps from $P_XL(gf)^*$ to $Lf^*Lg^*P_Z$ are the two associative expansions of that composition; the associativity identity of [lem-pod-integral-pullback-composition] identifies them before rationalization. Their rational images and their common-stage classes are therefore equal, by the definitions in [def-weil-derived-pullback-tensor-hom]. This is the equation test of Step 7 for the pullback composition comparison. For tensor the composition compatibility and naturality of $\mu$ in [lem-pur-derived-pullback-tensor-iso] give the same equation test for tensor-pullback comparisons; its associativity, symmetry and unit clauses give it for the tensor structure comparisons. All inputs and outputs are restricted to the already specified constructible domains.

Uses: lem-pod-integral-pullback-composition, def-weil-derived-pullback-tensor-hom, lem-pur-derived-pullback-tensor-iso.

### Returned step 10

Frobenius is semilinear over $k$, so apply the $k$-linear diagram theorems after the following relabeling. Replace the structural map $a_W:W\to\operatorname{Spec}k$ at a source corner of $g_W$ by $a_Wg_W$. Then $g_W$ to the original corner is $k$-linear, and a morphism $r$ between two such relabeled corners is $k$-linear because $rg_W=g_Vr$. These are still finite-type $k$-schemes: $g_W$ identifies each relabeled scheme with its original one. The sites, constant coefficient categories and underlying operation maps are unchanged, since the definitions depend on the underlying scheme morphisms. Thus all Frobenius faces of a composition diagram or exchange cube are diagrams to which [fix-lem-exchanges] applies. Its hypotheses require separated finite-type arrows and finite-type schemes, not separated structure maps $a_W$. Base-changed compactifications and the isomorphism faces retain the required arrow hypotheses.

Uses: fix-lem-exchanges, def-exchange-projection, def-weil-derived-pullback-tensor-hom.

### Returned step 11

Apply [fix-lem-exchanges](1),(2),(4) to the relabeled diagrams of Step 10, first with $P=R(-)_*$ and then with $P=R(-)_!$. Vertical pasting says that exchange for a composite is the composite of the two exchanges with the direct-image composition comparison inserted. This is exactly Step 7's equation for that comparison. For an exchange square, paste a Frobenius square with it in either order; both composites are exchange for the same outside square by horizontal and vertical pasting. Inserting the pullback and direct-image comparisons just proved equivariant yields Step 7's equation for the exchange transformation itself. Clause (4) intertwines all these maps with compactification refinement comparisons, so this proves the assertion for the specified compact-support operation, independent of its chosen representative. Naturality in the input then inserts its Weil map as in Step 7. The coefficient, witnessed-origin and finite-Tor restrictions in [fix-lem-exchanges] remain in force.

Uses: fix-lem-exchanges.

### Returned step 12

Write $H(M,N)=R\mathcal Hom(M,N)$ and $P=P_W$. For the canonical Hom transport $h:PH(M,N)\to H(PM,PN)$, the definition as transpose under the tensor/Hom adjunction of [sk-def-sf-operations](i) is the identity
$$\operatorname{ev}_{PM,PN}(1\otimes h)\mu_{M,H(M,N)}=P(\operatorname{ev}_{M,N}).$$
Here evaluation has domain $M\otimes H(M,N)$; this fixes the convention for $h$ in the standard lift. Naturality of evaluation in the isomorphisms $\theta_M:PM\to M$, $\theta_N:PN\to N$ gives
$$\operatorname{ev}_{M,N}(\theta_M\otimes H(\theta_M^{-1},\theta_N))=\theta_N\operatorname{ev}_{PM,PN}.$$
Compose these equalities. The tensor structure on $M\otimes H(M,N)$ is $(\theta_M\otimes H(\theta_M^{-1},\theta_N)h)\mu$, so the result is exactly $\operatorname{ev}\,\theta_{M\otimes H}=\theta_NP(\operatorname{ev})$. This proves evaluation equivariant on its stated domain, without inferring site-perfectness of arbitrary constructible objects.

Uses: sk-def-sf-operations, lem-pur-derived-pullback-tensor-iso.

### Returned step 13

For the ordinary projection transformation $\pi$ in [def-exchange-projection], its transpose $a_{u,M,N}$ is tensor-pullback followed by $\varepsilon_{u,M}\otimes1$. Both are equivariant by Steps 8–9, and $\pi=Ru_*(a)\eta$ is equivariant by Step 7. For the open projection comparison $\gamma$, compare its pullback under the compactification's Frobenius base-change map with the corresponding $\gamma'$ for $j'$. Apply $j'^*$ to this square, inserting the open base-change maps $\beta$ and the tensor/pullback comparisons. By [lem-sf-open-tensor-normalization], $j'^*\beta$ and the restrictions of $\gamma,\gamma'$ are identities after the open-unit identifications; the remaining square is the tensor/pullback composition equation from Step 9. Both original source and target are in the essential image of $j'_!$: use $\beta$ and $\gamma'$ to identify the source as well. Full faithfulness of $j'_!$ and its invertible unit, asserted in that same node, therefore reflect the restricted equality. This proves the required open comparison equation. Its strict-coefficient-system version in that node and the supplied higher-stage comparisons in [def-exchange-projection] retain this equation in the specified coefficient constructions. Now $\operatorname{PF}_{f,K,L}=Rp_*(\gamma)\pi_p$ is equivariant by composition and Step 11's compactification independence, on exactly its supplied tensor and finite-Tor domains.

Uses: def-exchange-projection, lem-sf-open-tensor-normalization.

### Returned step 14

A mate of any comparison now proved equivariant has, by [def-weil-pbc-adjunction-mate], three factors: a whiskered unit, the comparison under the appropriate lifted functors, and a whiskered counit. Steps 5–8 and 7 make each factor a Weil morphism, hence their composite is one. To identify it with an exceptional composition or exchange map, use [lem-weil-pbc-mate-pasting](1) for pasting on the non-adjoint sides, (2) for composition of adjunctions, and (3) for changing the adjunctions by the ordinary or compact-support comparison. These formulas identify the mate of the pasted square with the pasted mates for the very adjunctions fixed here. The bijection of [def-weil-pbc-adjunction-mate] ensures equality with the specified unit–map–counit definition, not merely an unspecified isomorphism of functors. In particular the conjugate of a composition comparison is equivariant; when it is invertible its inverse is equivariant by Step 7.

Uses: def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting.

### Returned step 15

These calculations take place in the rational/common-stage categories, so they apply to all their morphisms, including Weil maps without an invariant integral lattice. When a comparison is represented integrally, apply rationalization to its defining composites, and then take their classes over one common finite field, exactly as specified in [def-exchange-projection] and [def-weil-derived-pullback-tensor-hom]. Functors preserve the equality of these composites. Further coefficient extension conjugates source and target by the supplied comparison isomorphisms; the two adjacent intermediate comparisons cancel. Their identity and tower cocycles make the resulting equality independent of the representative. For every comparison whose invertibility is already known on this domain, Step 7 shows that its actual inverse is a Weil arrow, hence gives an isomorphism of Weil pairs. Nothing in this reasoning enlarges the domain or proves invertibility of another exchange or projection map.

Uses: def-exchange-projection, def-weil-derived-pullback-tensor-hom.

## What remains

No unresolved repair point. The four new unsplit statements are intentionally left for parallel future workers, as the human requested. No Lean was written or compiled. Required server dry-run and delivery results are recorded in the final tool output.
