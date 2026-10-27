# Q44 stage-1 repair report

## Files written

- `dag/nodes/sec-poincare-duality/lem-pod-formal-verdier-exchange-equivariance.json`: statement unchanged; four-step assembly, 2068 characters of proof text.
- `dag/nodes/sec-poincare-duality/lem-pod-verdier-pairing-three-transposes.json`: statement; unsplit; no Mathlib match. Isolates the projection/evaluation pairing and three explicitly typed adjunction transposes, including the rational dual-structure formula.
- `dag/nodes/sec-poincare-duality/lem-pod-verdier-composition-mate-normalization.json`: statement; unsplit; no Mathlib match. Isolates the structure-morphism mate and the comparison between the two substitution orders, identifying the precise inverse internal-adjunction component.
- `citations.json`: one verbatim statement excerpt per step/cited node.

## Attachments

None. The project search for the item tag has no hit. `WeilConjectures/WeilSheaf/VerdierDual.lean` states `AlgebraicGeometry.WeilComplex.nonempty_verdierDual_derivedLowerShriek_iso` using `sorry`, and only as existence of an isomorphism. It does not prove the specified evaluation-transposed arrow, coefficient comparisons and all domain clauses. The closed formal infrastructure in `PoincareDuality/Abstract.lean` concerns an abstract exchange with different input/output direction and no rational/common-stage Frobenius structures. Neither attaches the item.

## WANTED

None. The blueprint source and both auxiliary exchange/internal-adjunction proofs are available locally. This is an agent-written expansion of blueprint material, as the retained `proof_origin` says; it invokes no SGA source.

## Returned fault and repair

The released stage-1 repair note of 2026-10-22 explicitly reopens the item despite its old reviewed record. The sandbox contained only dispatcher marker files, with no node, report or search log. I copied the current live node, which contains exactly the returned eight steps, and kept its statement, statement dependencies, source, blueprint ancestry, searches and maintainer-owned fields. No earlier sandbox proof or report was discarded. No direct git command was run in the read clone.

The requested repair is substantive: two new, comparably sized tasks with empty proofs and empty proof dependency lists, not an unchanged push or a shorter restatement. The parent is 2068 characters. The first new statement has 3215 characters and the second 3849, including their complete contexts. Neither asserts the entire parent theorem. One ends before the dualizing composition identification; the other identifies this mate and the order of substitution, without asserting equivariance of the initial pairing or of all three transposes. Both are available to be split/proved independently; neither depends on the other or on the parent.

The source is `literature/blueprint/main-20261015/blueprint/sec-poincare-duality/sk-lem-finite/prop-weil-operations.proof.md`, sentence 4, together with the returned explicit expansion. I also read the current unit/operations statement, the chapter and unit records, and `main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-cor-verdier-exchange.proof.md` Steps 1--3 and `fix-lem-tensor-adjunction.proof.md` Steps 1--2. This stays on the supplied evaluation/adjunction route; it changes no chapter or unit route. Source references to the returned steps locate material in the existing repair baseline; the underlying blueprint location is stated explicitly too.

## Preservation of the eight old arguments

1. The duality, biduality, evaluation and scalar-extension assertions are retained by invoking the existing `cor-coef-verdier-weil-equivariance` in parent Step 1. The old orientation formula is an explicit conclusion of the first new node. To verify it, after inserting the tensor comparison, evaluation on the images of the structures is evaluation of the pulled-back functional on `theta_K^{-1} theta_K`; this is `theta_omega` applied to pulled-back evaluation. This uses the rational isomorphism directly. This calculation is material for the first new task, not a new proof step on an unsplit node.
2. The first new node keeps the specified projection direction, its inverse, evaluation in `FM tensor A` order, the Weil composition equation and inverse equation. Projection equivariance is supplied to the parent by the existing mate-coherence node; projection invertibility remains a hypothesis. There is no new projection-formula theorem hidden here.
3. The first new node specifies `t = G(b) eta^!` with its full domain and codomain; equivariance is the composition of the lifted image and the supplied equivariant unit.
4. The same node specifies `r = H_M(t) nu` and `s_M = Q(r) eta^*`, each on the exact object of the preceding adjunction. Their underlying maps are the stipulated Hom-bijection transposes by the unit formula.
5. The second new node keeps the pasted counit `epsilon^H H(epsilon^F)`, `alpha:HF -> U`, and the exact formula `c_Z = W(epsilon^{HF}_Z alpha^{-1}_{GJZ}) eta^U`. The existing mate definition fixes the direction; every factor is equivariant. At the coefficient unit it is the specified dualizing comparison, not a freely chosen isomorphism.
6. Parent Step 3 composes the equivariant arrow `QH_M(c)` from the second new node with the equivariant `s_M` from the first. It writes the Weil composition equation, identifying the exact requested formal map.
7. The second new node retains the equality between substituting `c` before the last two transposes and after them, and identifies the latter transposes with the inverse of the internal-adjunction comparison. The argument for the next worker is that `(v h)^sharp = R(v) h^sharp`, both equal to `R(v)R(h)eta`; apply it once to tensor--Hom and once to the ordinary adjunction. In the source's Hom chain, the image of the identity of `A` is precisely these three transposes; by Yoneda it is the inverse of the displayed internal-adjunction isomorphism. Thus it is the component `epsilon_M` defined by `def-sf-verdier-exchange-data`, so the canonical isomorphism theorem applies to this actual arrow. The extra admissibility and finite-Tor hypotheses are used only in this conditional identification/invertibility part.
8. Parent Step 4 keeps the inverse Weil equation explicitly. Multiplying `e theta_A = theta_B Phi(e)` by `e^{-1}` on the left and `Phi(e^{-1})` on the right gives it. The domain-only equivariance and absence of an integral-lattice requirement remain in the parent and both new statements.

The complete old proof text is preserved below for future workers, so no detail is lost through the extraction.

## Mathlib and duplicate searches

Before creating the nodes I searched the whole DAG by the notions, transposition/mate words and candidate ids; inspected the closest statements; and ran `tools/blueprint_refs.py ancestor` and the whole-blueprint searches `adjunction transpose equivariant`, `composition mate`, `Verdier exchange`, `evaluation transpose`, `dualizing composition`, and `Weil duality`. No imported blueprint node states either of the extracted normalization problems. The nearest ancestor is `prop-weil-operations`, with via `[lem-pod-formal-verdier-exchange-equivariance]`.

For each new node I ran leanfinder, leansearch, loogle and grep through the mandated `msearch.py` command. The two natural-language phrasings search each problem rather than only its chosen name. The exact queries and responses are retained in `searches.jsonl` and recorded in the node. All services responded. The interrupted calls had completed their log writes; I read those results instead of repeating the requests. The representation hits concern module representations, not derived sheaves and these three different adjunctions. Mathlib `Adjunction.homEquiv_unit`, `homEquiv_naturality_right` and `conjugateEquiv` are useful proof infrastructure, but none alone states the first construction or the second normalization and comparison with the specified internal-adjunction map. I read `Adjunction/Basic.lean` around 208--248, `Adjunction/Mates.lean` around 257--330, `Monoidal/Rigid/Basic.lean` around 378--425 and 576--589, and `RepresentationTheory/Rep/Basic.lean` around 804--833. These are not one-line specializations of one Mathlib result. Both new tasks therefore remain unsplit, with no fabricated leaf.

## Not duplicates

lem-pod-verdier-pairing-three-transposes vs cor-coef-verdier-weil-equivariance: the corollary gives duality/evaluation/biduality and scalar compatibility, but not the inverse-projection pairing and its three unit-normalized transposes; the new node assumes the lifted data and specifies those intermediate arrows.
lem-pod-verdier-pairing-three-transposes vs lem-pod-constructible-mate-coherence: the existing node gives the exceptional lift and generic comparison equivariance, but does not specify this pairing or the three intermediate arrows and their identification with successive transposes.
lem-pod-verdier-pairing-three-transposes vs lem-sfb-projection-internal-hom-formal: the abstract lemma asserts invertibility/naturality of a transposed map in categories with parametrized adjoints; it asserts no rational Weil equation or dual-structure formula. The new task concerns equivariance and exact intermediate arrows without an invertibility conclusion for their composite.
lem-pod-verdier-composition-mate-normalization vs lem-sf-dualizing-composition-coefficient-mate: the existing lemma gives the constructible composition mate and its scalar equation; the new task gives its Weil equation together with substitution across the last two transposes and identification of that precise map with the inverse internal-adjunction component.
lem-pod-verdier-composition-mate-normalization vs def-sf-verdier-exchange-data: the definition specifies epsilon and stage-conclusion predicates; it does not prove equality with substitution after transposition. The new statement proves that identity for the specified mate.
lem-pod-verdier-composition-mate-normalization vs fix-cor-verdier-exchange: the existing theorem gives a canonical exchange isomorphism under admissibility and finite-Tor assumptions. The new node identifies two concrete construction orders, with the mate/substitution identity also meaningful outside that invertibility domain.
lem-pod-verdier-composition-mate-normalization vs fix-lem-tensor-adjunction: that theorem has the opposite comparison direction and no dualizing composition mate or substitution-order identity. The new task identifies the explicit three-transpose arrow with its inverse.
lem-pod-verdier-composition-mate-normalization vs lem-coef-internal-adjunction-pairing-change: that lemma compares finite quotient coefficients for a locally closed immersion and ordinary small-etale derived modules; it neither treats rational Weil pairs nor the structure-composition substitution order.
lem-pod-verdier-composition-mate-normalization vs lem-pur-rational-weil-naturality-mate: that lemma is a smooth purity naturality/mate assertion with a Tate twist and relative dimension, absent here; it does not identify a Verdier-exchange transpose.
lem-pod-verdier-composition-mate-normalization vs lem-pod-structure-identity-mate: the identity-mate node handles a_Y=id at the point only; no exchange construction or substitution-order identity is asserted there.
lem-pod-verdier-composition-mate-normalization vs lem-sf-composition-projection-mate: the latter is a projection/compositor identity at finite coefficients and strict systems; it does not involve exceptional transposes, rational Frobenius equations or the internal-adjunction inverse.
lem-pod-verdier-composition-mate-normalization vs lem-pur-ordinary-derived-composite-transpose: the latter concerns only ordinary pullback/direct-image composite adjunctions at finite coefficients, not the three different adjunctions and the dualizing mate here.
lem-pod-verdier-composition-mate-normalization vs lem-pur-adjunction-evaluation-composition: the latter compares realization compositors of six unrelated adjunctions; it does not give the Verdier substitution/transposition identity.
lem-pod-verdier-composition-mate-normalization vs lem-pur-constructible-tensor-composition: the latter is a cohomological-smoothness tensor-composition assertion at finite coefficients, not the duality-exchange normalization in rational Weil categories.
lem-pod-verdier-pairing-three-transposes vs lem-pod-formal-verdier-exchange-equivariance: the new node stops at QH_M(G omega_Y); it does not identify G omega_Y with omega_X, assert exchange invertibility or supply duality scalar/biduality compatibility.
lem-pod-verdier-composition-mate-normalization vs lem-pod-formal-verdier-exchange-equivariance: the new node supplies the mate and normalization; it does not prove that the initial pairing or its three transposes are equivariant and does not supply the parent's duality/coefficient assertions.

## Review by Q44

I read delivery-errors B--E in full and checked each issue against the actual statements and the source. Both new statements introduce all their fields, schemes, coefficients, Frobenius functors, Weil pairs, domains and adjunctions, with definition dependencies. Their statements contain formulas and assertions, not proof sketches; the proof material is here in the report. They use TeX with single escapes, real source paths and precise places, empty proof lists, real recorded searches and explicit blueprint ancestry. No claim relies on a nonexistent Mathlib index or treats a sorried upstream theorem as a proof.

For parent Step 1 I opened `cor-coef-verdier-weil-equivariance`: its statement explicitly gives the contravariant Weil dual, evaluation/biduality, both scalar comparisons and the named compatibility diagrams. Its schemes are separated and of finite type, as required here, and its coefficient stages are exactly E and the common-stage algebraic closure. The old dual formula was only orientation in the parent; it is now part of the first new task's explicit statement, with its evaluation-compatible Hom comparison supplied in the hypotheses.

For parent Step 2 I opened `lem-pod-constructible-mate-coherence`: its statement expressly says the projection transformation is a Weil morphism on its constructible domains. I do not extract projection invertibility from it. I opened `def-exchange-projection` to check the direction FM tensor A -> F(M tensor PA); the first new node has that same direction and uses its inverse. The first new statement supplies exactly b,t,r,s_M and their equivariance, not just a generic adjunction existence theorem. I verified t has domain V, r has domain PA and s_M has domain A, so the three supplied units are applied to the correct objects.

For parent Step 3 I opened the second new statement, `def-weil-pbc-adjunction-mate`, and `def-sf-verdier-exchange-data`. With alpha:HF -> U its inverse starts at U, so the displayed counit composite starts at U(GJZ) and its transpose has type GJZ -> WZ. Thus it is the specified c, and QH_M(c) really maps QH_M(G omega_Y) to QH_M(omega_X). The new node's conclusion explicitly gives its Weil equation. The remaining composition is the defining equation for Weil arrows, written in the assembly. No non-elementary result is borrowed from another node's proof.

For parent Step 4 I opened both `fix-lem-tensor-adjunction` and `fix-cor-verdier-exchange` as well as the normalization definition. The former comparison has direction QH_M(GN) -> Hom(FM,N); the arrow from A must be its inverse. The second new node's statement supplies exactly that identity, the equality of substitution orders and the identification with epsilon. I retained the conditional exceptional-admissibility and finite-Tor hypotheses for invoking those isomorphism theorems; they are not smuggled into the earlier formal equivariance argument. The inverse Weil equation is multiplication of an equality by inverses, and needs no new lemma. I retained the existing off-unit tool-use declarations for the duality corollary and these two conditional theorems; no alternative unit route is introduced.

I checked f=id, M=0, X empty, the geometric point with nonsemisimple/Jordan Frobenius, and scalar extension E subset L. For f=id the units and mate have their identity normalizations and both substitution orders agree; for zero or empty inputs all typed arrows are the unique relevant arrows; Jordan Frobenius still supplies theta^{-1} and no stable lattice is needed. None of these checks uses site-perfectness or semisimplicity. The new statements assume the displayed operations exist on a domain rather than assert unconditional preservation outside it. No statement correction or STATEMENT-DISPUTED is needed.

I checked citation coverage against the statements, not just the ids. `citations.json` contains verbatim excerpts for every cited node of every parent step. All four proof steps are below 2000 characters, and the whole assembly is below 3000. The only long tasks are the two statement-only nodes requested by the human. The old eight arguments are accounted for above and copied verbatim below; no argument was blurred to meet the length bound. No Lean, compiler, Lake, agent launch, repository write or launcher edit was performed.

## Unfinished work and verification

Both new nodes are intentionally unsplit, for independent later workers. No other mathematical work is left on this assigned repair. Server dry-run and push results will be recorded here after completion.

## Original eight-step proof (verbatim repair baseline)

### Old Step 1

Apply [cor-coef-verdier-weil-equivariance] to each of $T_0=X_0,Y_0$. Its hypotheses are exactly the separated finite-type finite-field and rational/common-stage coefficient hypotheses here. It gives the contravariant Weil lift of $D_T$, equivariance of evaluation and biduality, and the dualizing/duality scalar-extension comparisons together with their evaluation, biduality and exceptional-adjunction diagrams. In particular $A=D_YRf_!M$ has its specified Weil structure whenever $Rf_!M$ is in the stated constructible domain. For orientation only (nothing below uses the formula): writing $h_T:P_TR\mathcal Hom(K,\omega_T)\simeq R\mathcal Hom(P_TK,P_T\omega_T)$, the structure $R\mathcal Hom(\theta_K^{-1},\theta_{\omega_T})h_T$ makes evaluation equivariant, since $\operatorname{ev}(\theta_Kx,\theta_D\varphi)=\theta_{\omega_T}((h_T\varphi)(\theta_K^{-1}\theta_Kx))$; it uses the rational isomorphism $\theta_K$ itself. Steps 2--8 use only the equivariance assertions of the corollary. The cited corollary also gives these assertions in the common-stage category without a stable integral lattice.

Uses: cor-coef-verdier-weil-equivariance

### Old Step 2

Write $F=Rf_!$, $G=Rf^!$, $P=Lf^*$ and $Q=Rf_*$, and put $V=M\otimes^L PA$. The projection isomorphism $\operatorname{PF}:FM\otimes^L A\xrightarrow{\sim}FV$ of [def-exchange-projection] is a morphism of Weil pairs on this domain by [lem-pod-constructible-mate-coherence], whose statement makes the projection transformation of [def-exchange-projection] a Weil morphism on its constructible domains for the same separated finite-type $f_0$ and the same rational/common-stage Weil pairs; its invertibility is the hypothesis of the item, not a consequence of equivariance. Its inverse is a Weil morphism: if $u\theta_B=\theta_CP_Y(u)$, multiplication by $u^{-1}$ on the left and $P_Y(u^{-1})$ on the right gives $u^{-1}\theta_C=\theta_BP_Y(u^{-1})$. The evaluation $FM\otimes^L D_YFM\to\omega_Y$ is equivariant by Step 1. Consequently $b=\operatorname{ev}\circ\operatorname{PF}^{-1}:FV\to\omega_Y$ is equivariant. Indeed for two composable Weil arrows $u,v$, $(vu)\theta=v\theta'P_Y(u)=\theta''P_Y(vu)$, the defining equation of [def-weil-weil-sheaf-complex]. The displayed evaluation uses the $FM\otimes A$ order, so no symmetry needs to be inserted.

Uses: def-weil-weil-sheaf-complex, cor-coef-verdier-weil-equivariance, lem-pod-constructible-mate-coherence, def-exchange-projection

### Old Step 3

For the assumed lifted exceptional adjunction $F\dashv G$, with unit $\eta^!$, the first transpose is exactly $t=G(b)\circ\eta^!_V:V\to G\omega_Y$. Both factors are arrows of Weil pairs: $G(b)$ because $G$ is the supplied lifted functor, and $\eta^!_V$ because its unit is assumed equivariant. Thus $t$ is equivariant by the composition equation of Step 2. This only uses the constructible lifted adjunction stipulated in the statement, and does not assume an ambient exceptional right adjoint.

Uses: 

### Old Step 4

Let $H_M=R\mathcal Hom_X(M,-)$ and let $\nu$ be the unit of the stipulated lifted adjunction $M\otimes^L-\dashv H_M$. The second transpose is $r=H_M(t)\circ\nu_{PA}:PA\to H_M(G\omega_Y)$. Its factors are Weil arrows by functoriality of the lifted $H_M$ and equivariance of $\nu$. For the lifted ordinary adjunction $P\dashv Q$ with unit $\eta^*$ the third transpose is $s=Q(r)\circ\eta^*_A:A\to QH_M(G\omega_Y)$. The same two assertions for $Q$ and $\eta^*$ make $s$ equivariant. These are the unit-then-right-adjoint formulas for the given adjunction bijections, so their underlying maps are precisely the successive transposes specified in the statement.

Uses: 

### Old Step 5

Here is the mate expression for $c$. Set $H=Ra_Y{}_!$, $J=Ra_Y^!$, $U=Ra_X{}_!$, $W=Ra_X^!$, and let $\alpha:HF\xrightarrow{\sim}U$ be the stipulated compact-support compositor. The counit of the pasted adjunction $HF\dashv GJ$ is $\varepsilon^{HF}_Z=\varepsilon^H_Z\circ H(\varepsilon^F_{JZ})$. Transposing $\varepsilon^{HF}_Z\circ\alpha^{-1}_{GJZ}:U(GJZ)\to Z$ through $U\dashv W$ gives
$$c_Z=W(\varepsilon^{HF}_Z\circ\alpha^{-1}_{GJZ})\circ\eta^U_{GJZ}:GJZ\longrightarrow WZ.$$
This is the unit–map–counit mate formula of [def-weil-pbc-adjunction-mate], applied to $\alpha^{-1}:U\to HF$ and the pasted adjunction. Each unit, counit and $\alpha$ is equivariant by hypothesis, its inverse is equivariant by Step 2, and the displayed lifted functors preserve Weil arrows. Hence $c_Z$ is equivariant. At $Z=\Lambda_s$, with its coefficient-unit Weil structure, this is the specified $c:G\omega_Y\simeq\omega_X$. The specified compositor and pasted adjunctions fix this mate; no independent choice of dualizing identification is being made.

Uses: def-weil-pbc-adjunction-mate

### Old Step 6

The given lift of $H_M$ sends the Weil arrow $c$ to $H_M(c)$, and the given lift of $Q$ sends that arrow to $QH_M(c)$. Thus
$$e_M=QH_M(c)\circ s:D_YFM\longrightarrow QD_XM$$
is equivariant, by Steps 4–5 and the composition equation of Step 2. This is exactly the requested formal map: $b$ was the specified inverse projection followed by evaluation, $s$ its three successive transposes, and the last factor is the specified substitution of $c$. All of these arguments use just the lifted data on the domain in the question; none enlarges that domain or asserts a new invertibility theorem.

Uses: 

### Old Step 7

Under the additional hypotheses of [fix-lem-tensor-adjunction, fix-cor-verdier-exchange], use their canonical exchange in the normalization [def-sf-verdier-exchange-data]. That definition specifies its arrow $\epsilon_M$ by projection and evaluation, exceptional transposition, substitution of $c$, then tensor–Hom and ordinary transposition. Moving substitution of $c$ past the latter two transposes changes neither map: for any adjunction $L\dashv R$, the unit formula gives $(v h)^\sharp=R(v)h^\sharp$, since both sides are $R(v)R(h)\eta$. Apply this first to $M\otimes-\dashv H_M$ and then to $P\dashv Q$. Therefore $\epsilon_M=e_M$, including the specified projection map and composition mate. In this normalization the internal-adjunction comparison has the direction stated in [fix-lem-tensor-adjunction], so the arrow from $D_YFM$ is its inverse followed by $QH_M(c)$, as specified by the auxiliary exchange in [def-sf-verdier-exchange-data]. The canonical isomorphism of [fix-cor-verdier-exchange] is, through its statement dependency [def-sf-verdier-exchange-data], a stage conclusion, whose components are by that definition exactly the arrows $\epsilon_M$; so its isomorphism assertion applies to this same arrow $\epsilon_M=e_M$. This invocation retains its exceptional admissibility and finite-Tor hypotheses only for this invertibility assertion.

Uses: fix-lem-tensor-adjunction, fix-cor-verdier-exchange, def-sf-verdier-exchange-data

### Old Step 8

If $e_M$ is invertible, its Weil equation $e_M\theta_A=\theta_{QD_XM}P_Y(e_M)$ gives
$$e_M^{-1}\theta_{QD_XM}=\theta_AP_Y(e_M^{-1})$$
by the same multiplication as in Step 2. Thus its inverse is also equivariant. Steps 2–6 did not use the extra hypotheses of Step 7, so they also establish the stated equivariance on every domain supplying the displayed formal data. They used only rational Weil maps and lifted units/counits, never reduction of a rational Frobenius automorphism on an invariant integral lattice.

Uses: 
