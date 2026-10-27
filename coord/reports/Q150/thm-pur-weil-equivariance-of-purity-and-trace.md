# Q150 repair: Weil equivariance of purity and trace

## Files written

- `dag/nodes/sec-six-functors/thm-pur-weil-equivariance-of-purity-and-trace.json`: existing statement unchanged; six-step assembly, 2290 characters of proof text.
- `dag/nodes/sec-six-functors/lem-pur-finite-geometric-purity-mate.json`: statement, unsplit; no Mathlib match. The finite retagging, orientation/tensor comparison and counit-mate identification from old Steps 1–2.
- `dag/nodes/sec-six-functors/lem-pur-tower-geometric-purity-mate.json`: statement, unsplit; no Mathlib match. The comparison in the ordinary derived category of coefficient towers from old Step 6.
- `dag/nodes/sec-six-functors/lem-pur-integral-geometric-comparison-realization.json`: statement, unsplit; no Mathlib match. Identification of the realized semilinear comparison diagram with the actual integral diagram, from old Step 10.

All three new nodes have empty proofs and proof dependencies, null proof origin and Mathlib match, explicit source places, and blueprint ancestry through the item with empty via lists. Their statements have respectively 2472, 2564 and 3329 characters. Each is a map-comparison problem without a strict Weil datum or an equivariance conclusion. The finite, tower and integral arguments can be assigned separately; no new node contains the theorem's full assertion.

`citations.json` records one verbatim statement excerpt for every citation of every assembly step. `searches.jsonl` and the individual search output files retain the searches actually executed; `old-proof.json` and the archive below retain the complete returned argument.

## Attachments

None. Searching the live `lean/WeilConjectures/` for the exact blueprint tag and the notions found `AlgebraicGeometry.Etale.exists_tateOrientation_isWeilMorphism_untwistedSmoothTrace` at `EtaleCohomology/PoincareDuality/Frobenius/TraceEquivariance.lean:57` (the docstring begins at 50). Its proof is `sorry`. It treats finite coefficients for a structure morphism to the geometric point, and does not give all three assertions for an arbitrary smooth relative morphism and all coefficient stages. `WeilDual.lean` and `DualTateData.lean` use this equivariance as a hypothesis. None supplies an attachment for the item or the three comparison lemmas.

## WANTED

None. These tasks continue the agent-written current blueprint proof and its existing purity/base-change and integral-adjunction refinements; they do not introduce an unavailable literature route. No SGA source is used.

## What was wrong and what changed

The human return required redistributing a 9760-character proof among at least three new statement-only tasks and leaving an assembly of at most 3000 characters. The sandbox initially contained only dispatcher briefs, so I recovered the delivered argument from the current repository node. I preserved its complete statement, original searches, source metadata, blueprint update, import flags, Lean audit, and existing tool-use records. The inherited statement-dispute explanation records the previous semilinear typing repair; I made no new statement change. The new tasks isolate the three substantial comparison arguments instead of restating purity, counit and trace equivariance as three lemmas.

The ordinary adjunction calculation is shared between finite coefficients and actual coefficient towers. This is the same computation twice, with both categories explicitly covered by assembly Steps 1–4. It retains the naturality, transpose, counit and exchange equations; it does not infer a tower equation from agreement of evaluations. Old Step 11 remains as the explicit field transport in assembly Step 6.

## Not duplicates

lem-pur-finite-geometric-purity-mate vs det-sp-purity-bc-factors: the existing statement assumes a Cartesian square of k-morphisms; the new statement identifies the original unretagged purity and its canonical Tate comparison with the counit mate for a semilinear geometric-Galois square, including the tensor-map comparison under retagging.
lem-pur-finite-geometric-purity-mate vs lem-pur-orientation-ground-field-retagging: the existing statement identifies orientations only; the new statement also identifies the tensor-map transpose and the purity exchange with the specified compact-support mate.
lem-pur-finite-geometric-purity-mate vs thm-pur-smooth-base-change-coherence: that statement has k-linear squares and a purity-defined smooth exchange; it does not identify that exchange with the counit mate on the unretagged semilinear square.
lem-pur-finite-geometric-purity-mate vs pur9-cs-def-bc: the latter defines a map on a k-linear square; it does not prove that its map agrees with the semilinear purity composite.
lem-pur-tower-geometric-purity-mate vs lem-pur-tower-purity-ground-field-retagging: the existing statement identifies retagged purity; the new task also compares the pulled purity with the whole-tower compact-support counit mate for the semilinear Cartesian square.
lem-pur-tower-geometric-purity-mate vs det-sp-tower-exceptional-bc: the existing statement supplies k-linear tower exchange, but does not identify it with the purity composite for the original semilinear square.
lem-pur-tower-geometric-purity-mate vs det-sp-purity-bc-factors: the existing statement compares factors for k-linear squares, whereas the new task includes their identifications on the original semilinear sites with the canonical roots-of-unity tower comparison.
lem-pur-integral-geometric-comparison-realization vs det-sp-integral-adjunction-bijection: the existing statement realizes vertical operations, adjunction and purity; the new task identifies horizontal semilinear pullbacks and the whole comparison diagram, including compact-support exchange and its actual mate.
lem-pur-integral-geometric-comparison-realization vs det-sp-tower-exceptional-bc: its integral clause only treats E=Q_l and k-linear squares; the new statement uses every finite E and identifies the canonical semilinear diagram, with its purity and Tate maps.
lem-pur-integral-geometric-comparison-realization vs lem-cbc-exact-product-functor-strict-limit: that general comparison assumes exact products and supplies a limit comparison alone; the new statement specifies the geometric inverse-image equivalence and its K-injective comparison and identifies the full purity/adjunction/exchange diagram.
lem-pur-integral-geometric-comparison-realization vs lem-weil-isomorphism-derived-pullback-reduction-tower: that identifies the strict quotient reductions; it does not identify derived-limit purity, compact-support, counit and mate maps.
lem-pur-integral-geometric-comparison-realization vs lem-trf-integral-pullback-comparison-realization: the existing statement constructs composition and scalar-extension comparisons of completed pullback; it does not compare the smooth exceptional adjunction diagram with the realized semilinear tower diagram.
lem-pur-integral-geometric-comparison-realization vs lem-fd-whole-tower-integral-pullback-comparison: that compares framework and PBC pullbacks and scalar associators; the new task concerns the smooth compact-support/exceptional adjunction, its purity and counit-mate exchanges.

The existing `lem-pur-rational-weil-naturality-mate` has rational coefficients and a descended compactification; it is neither a finite nor a tower nor a completed integral comparison. The existing rational constructible mate-coherence node concerns a Weil lift once the mate is supplied, not either geometric purity comparison. The blueprint search for semilinear, retagging, counit equivariance, realization, purity and strict derived-limit found no blueprint node stating any of the three new assertions. DAG keyword and statement searches were across all chapters, and the closest candidates above were opened and compared. No new Stacks tag is introduced, hence there is no same-tag pair omitted here.

## Review by Q150

I read the current main-20261015 `thm-pur-weil-equivariance-of-purity-and-trace.proof.md`, the base-change factors statement and its unit `_section.md`, and `sk-prop-sp-integral-adjunction-bijection.md`. The chapter and six-operations package unit keep the diagonal/deformation purity route and the constructible adjunction; this repair does not change them. The unit's key node is `sk-thm-sf-package`, not this item, so no unit record is changed.

For the finite task I checked the statements of `det-sp-purity-bc-factors`, `lem-trf-adjoint-mate`, `lem-pur-orientation-ground-field-retagging`, `def-pur-smooth-purity-map`, `pur9-cs-def-bc`, `thm-cbc-finite-level-proetale`, `lem-sf-proetale-constructible-origin`, `lem-weil-isomorphism-derived-pullback` and `def-weil-frobenius-coefficient-twists`. The arbitrary finite coefficient exponent is retained; no divisibility by the ramification index is assumed. Bounded constructible origin supplies the CBC domain; the separated finite-type geometric schemes are qcqs and admit the required compactification. Retagging changes only the ground-field structural map: the small sites, diagonal over Y, compactification, tensor symmetry, projection map and counit agree under the counit-preserving right-adjoint identification. Thus the actual transpose, not only the dualizing object, is the comparison task. The root comparison is the specified tau_d; no extra q-factor appears. The new task states the exact derived-map equality that assembly Step 1 needs.

For the tower task I opened `det-sp-tower-gluing`, `det-sp-tower-gamma`, `lem-pur-tower-purity-ground-field-retagging` and `det-sp-tower-exceptional-bc`. They supply actual derived tower morphisms, naturality and the transpose formula, not a rule that evaluations detect equality. The task retains uniform cohomological and Tor bounds, ordinary tower tensors, all quotient transitions and the canonical root tower. It permits nonnormalized inputs; the integral application subsequently uses normalized reduction towers. The distinct finite and tower tasks therefore do not introduce a false levelwise lifting assertion.

For the integral task I read `det-sp-normalized-equivalence`, `det-sp-integral-adjunction-bijection`, `det-sp-integral-direct-image-tower`, `lem-weil-proetale-isomorphism-inverse-image` and `lem-weil-isomorphism-derived-pullback`. I also compared the quotient-tower, exact-product strict-limit and framework/PBC comparison candidates listed above. Finite type over k supplies Noetherianity whenever the constructible equivalence is used. Reconstruction at the input uses only the derived-complete unit, as the old proof specifies. Exact site inverse-image equivalences extend to completed module sheaves through the actual inverse-limit coefficient isomorphism and then to strict towers. For an acyclic test complex, its Hom complex into the image of a K-injective complex identifies with the Hom complex from its acyclic inverse image; hence that image is K-injective. Preservation of ordinary limits then gives the derived comparison. The new task requires these specified comparisons to identify B, e, b, purity and the counit simultaneously. This is more than the existence of unrelated object isomorphisms, and retains the old proof's substantive missing comparison as open work for another worker.

For assembly Step 1 I checked both new statements give exactly e Q Gamma = Gamma b and hence e=E by cancellation. For Step 2 the finite naturality node says purity is natural in K; the tower-gamma node explicitly says its isomorphism is natural in the entire tower. The two defining composites in the Tate-datum statement are exactly a=H(phi)b and c=G(phi)e. Step 3 uses the adjunct-counit node's exact transpose equation and the transport definition F(phi_M)B_M; its remaining equality is counit naturality with the typed counit at K, adjunct to 1_GK. Step 4 uses naturality of B, the preceding purity equality and the trace composite epsilon F(Gamma) from the smooth-trace definition, and then substitutes Step 3. These are elementary compositions with the cited maps, and all factors have the displayed source and target. Step 5 uses the integral task's identification of every named map with its realization, so functoriality applies to the full diagrams. Step 6 uses the explicit integral-origin/common-stage restriction of this item's Tate datum, the rational purity transport, trace coherence and the higher-coefficient transport prescription in `def-exchange-projection`. It makes no assertion about an arbitrary rational Weil isomorphism without an integral-origin datum. Common-stage extension leaves the morphism class unchanged.

I tested the statements on f=id, d=0, K=0, the empty source, the first quotient and ramified E. For f=id and d=0 the counit-mate formula reduces to the canonical pullback identification. K=0 and the empty source make every required map the unique map on zero objects. The first finite quotient has the same canonical root comparison. Ramification changes the cofinal powers but not the O_E/ell^m tower used by the retained integral argument. No arbitrary-site claim that inverse image commutes with limits is made: the horizontal maps are scheme isomorphisms. No scheme-Frobenius square is claimed Cartesian.

I checked B–E point by point: self-contained objects and coefficient categories; every bracketed notion in a new statement is in its statement dependencies; three kinds of executed Mathlib search plus a second semantic phrasing per task; the closest hits concern ordinary algebra/module adjunctions or ring Frobenius and do not give these geometric diagram identities; no proof hidden inside a new unsplit statement; exact quotation checks; no changed target statement or new hypothesis; no new conclusion weakened. The assembly's six steps are each below 2000 characters. The three difficult comparisons remain explicit open nodes; their old detailed arguments are preserved below for the workers who take them, without inserting proof steps into their unsplit node files.

## Argument preservation map

- Old Steps 1–2: finite task. All finite-site origin and CBC hypotheses, retagged k-linearity, equality of orientation and tensor-map transposes, finite exceptional mate definition, root normalization, and cancellation to E are retained in the task's interface and the archived argument.
- Old Steps 3–5: assembly Steps 2–4 in the finite category, with every intermediate displayed equality retained.
- Old Step 6: tower task. Its statement retains equality in the derived tower category, both transpose and purity formulas, root-tower comparison, and retagged orientation and tensor maps.
- Old Steps 7–9: assembly Steps 2–4 in the tower category, using tower naturality and the same explicit calculations. Each intermediate equality appears once, quantified over both categories.
- Old Step 10: integral task and assembly Step 5. The K-injective equivalence and ordinary/derived-limit identification, completed coefficient ring, reconstruction unit, and realized purity, adjunction, compact support and exchange maps all remain explicit.
- Old Step 11: assembly Step 6. Rationalization, integral-origin data, common finite coefficient stage, compatibility with extension and equality of common-stage classes are retained.

## Complete returned proof, retained for the new tasks

The following is the original eleven-step proof verbatim. This archive is not a proof field of any new node and does not mark any of them split.

### Returned step 1

First work at an arbitrary finite coefficient ring $A=A_{E,n}$. The first square of [def-pur-scheme-geometric-frobenius] is Cartesian, with horizontal scheme isomorphisms. Write $F=Rf_!$, $G=Rf^!$, and $P,Q,H,b$ as in the statement, and let $B_M:PFM\simeq FQM$ be compact-support exchange. This is an isomorphism by [thm-cbc-finite-level-proetale]: the complexes used below, $GK$ and $HK\simeq GK$, are bounded constructible and have etale-origin witnesses by [lem-sf-proetale-constructible-origin]. Inverse image along the horizontal isomorphisms preserves the relevant categories by [lem-weil-isomorphism-derived-pullback]; there is no use of a Cartesian square of scheme Frobenius. The twist part of $b$ is the roots-of-unity inverse-image comparison defining $\tau_d$ in [def-weil-frobenius-coefficient-twists]. In particular no extra scalar is to be inserted into $b$.

Cited nodes: def-pur-scheme-geometric-frobenius, thm-cbc-finite-level-proetale, lem-sf-proetale-constructible-origin, lem-weil-isomorphism-derived-pullback, def-weil-frobenius-coefficient-twists.

### Returned step 2

Retag the structural maps of the source copies $X,Y$ by $\operatorname{Spec}(\gamma)$. Then $g_X:X^{\langle\gamma\rangle}\to X$ and $g_Y:Y^{\langle\gamma\rangle}\to Y$ are $k$-morphisms: $a_Xg_X=\operatorname{Spec}(\gamma)a_X$, and likewise for $Y$. Their square has vertical maps $f^{\langle\gamma\rangle},f$ and is Cartesian as before. Thus [det-sp-purity-bc-factors] applies in its standing $k$-linear setting. On the underlying sites identify the two compact-support functors using the same compactification, and the right adjoints by the counit-preserving uniqueness isomorphism of [lem-trf-adjoint-mate]. The orientation equality of [lem-pur-orientation-ground-field-retagging] identifies the orientation for $f^{\langle\gamma\rangle}$ with that for $f$. The remaining tensor map of [def-pur-smooth-purity-map] is the transpose of the same symmetry, inverse projection map and counit composite on the identical underlying sites; equality of these transposes identifies the tensor maps. Consequently the purity map for the retagged $f$ is the original purity map.

Let $e_K:QGK\to GPK$ be the transpose of $m_K=P(\varepsilon_K)B_{GK}^{-1}:FQGK\to PK$. This is the finite exceptional base-change map $b_{v,K}$ of [pur9-cs-def-bc] (defined there as exactly this transpose of the pulled-back counit composed with the inverse compact-support exchange), which is the comparison $e_f$ under which the cited base-change factors node is stated. Applying its orientation and tensor-map clauses to the now $k$-linear square, and composing with shift reassociation, gives
$$e_K\circ Q(\gamma_{f,K})=\gamma_{f,PK}\circ b_K.$$
The Tate-line comparison here is the canonical $\tau_d$ of Step 1. Cancellation of $Q\gamma_{f,K}$ gives $e_K=E_K$. Thus the purity-defined exchange is the counit mate; this identification has not been assumed in the definition of $E$.

Cited nodes: det-sp-purity-bc-factors, lem-trf-adjoint-mate, lem-pur-orientation-ground-field-retagging, def-pur-smooth-purity-map, pur9-cs-def-bc.

### Returned step 3

Naturality of purity in its coefficient object, [prop-pur-smooth-purity-naturality-cover], applied to $\varphi_K:PK\to K$ gives $G(\varphi_K)\circ\gamma_{f,PK}=\gamma_{f,K}\circ H(\varphi_K)$. Combine this with Step 2:
$$\varphi^!_{f,K}\circ Q\gamma_{f,K}=G(\varphi_K)e_KQ\gamma_{f,K}=\gamma_{f,K}H(\varphi_K)b_K=\gamma_{f,K}\varphi^{\mathrm{pur}}_{f,K}.$$
The first and last equalities are the two defining composites of [def-pur-tate-datum]. This is the first displayed square.

Cited nodes: prop-pur-smooth-purity-naturality-cover, def-pur-tate-datum.

### Returned step 4

By the adjunct-counit identity [lem-weil-pbc-adjunct-counit-identity], the definition of $e_K$ gives $\varepsilon_{PK}\circ F(e_K)=P(\varepsilon_K)\circ B_{GK}^{-1}$. Naturality of the counit at $\varphi_K$ gives $\varepsilon_K\circ FG(\varphi_K)=\varphi_K\circ\varepsilon_{PK}$. Therefore, using $e_K=E_K$ and the transport formula of [def-pur-compact-support-transport],
$$\begin{aligned}
\varepsilon_K\circ\varphi_{F GK}
&=\varepsilon_K\circ F(G(\varphi_K)e_K)\circ B_{GK}\\
&=\varphi_K\circ\varepsilon_{PK}\circ F(e_K)\circ B_{GK}
=\varphi_K\circ P(\varepsilon_K).
\end{aligned}$$
This is precisely exceptional-counit equivariance. The counit is the counit at $K$, that is, the adjoint transpose of the identity on $GK$, not of an ill-typed identity on $K$.

Cited nodes: lem-weil-pbc-adjunct-counit-identity, def-pur-compact-support-transport.

### Returned step 5

Put $a=\varphi^{\mathrm{pur}}_{f,K}$ and $c=\varphi^!_{f,K}$. Naturality of $B$ at $\gamma_{f,K}:HK\to GK$ and Step 3 yield
$$\begin{aligned}
F(\gamma_{f,K})\circ\varphi_{FHK}
&=F(\gamma_{f,K})\circ F(a)\circ B_{HK}\\
&=F(c)\circ FQ(\gamma_{f,K})\circ B_{HK}
=F(c)\circ B_{GK}\circ PF(\gamma_{f,K})
=\varphi_{FGK}\circ PF(\gamma_{f,K}).
\end{aligned}$$
Postcompose by $\varepsilon_K$ and use Step 4. By [def-pur-smooth-trace], $\varepsilon_K F(\gamma_{f,K})=\operatorname{Tr}^{\mathrm{sm}}_{f,K}$, so this says
$$\operatorname{Tr}^{\mathrm{sm}}_{f,K}\circ\varphi_{FHK}=\varphi_K\circ P(\operatorname{Tr}^{\mathrm{sm}}_{f,K}),$$
the second displayed square. Both transported data here are exactly those of [def-pur-compact-support-transport].

Cited nodes: def-pur-smooth-trace, def-pur-compact-support-transport.

### Returned step 6

Work in the ordinary derived category of coefficient towers $A_\bullet=\mathcal O_E/\ell^\bullet$. Put $F=Rf_{!,\bullet}$, $G=f^!_\bullet$ using [det-sp-tower-gluing], and $H=f_\bullet^*(-)(d)[2d]$, $\gamma:H\simeq G$ using [det-sp-tower-gamma]. Write $P,Q$ for the horizontal pullbacks. Retag the source field structures as in Step 2. The full tower purity comparison is unchanged under these underlying-site and counit-preserving identifications by [lem-pur-tower-purity-ground-field-retagging]. Apply [det-sp-purity-bc-factors] to this $k$-linear square in its tower case. If $B:PF\simeq FQ$ and $e:QG\simeq GP$ are the tower exchanges of [det-sp-tower-exceptional-bc], it gives
$$e_K\,Q(\gamma_K)=\gamma_{PK}b_K,\qquad e_K=\gamma_{PK}b_K(Q\gamma_K)^{-1}.$$
Here $b:QH\simeq HP$ includes the Tate comparison already fixed in Step 1. The cited tower exchange is explicitly the transpose of $P(\varepsilon_K)B_{GK}^{-1}$. All comparisons and this equality are in the tower category before evaluation or inverse limit.

Cited nodes: det-sp-tower-gluing, det-sp-tower-gamma, lem-pur-tower-purity-ground-field-retagging, det-sp-purity-bc-factors, det-sp-tower-exceptional-bc.

### Returned step 7

Let $\phi:PK\simeq K$ be the compatible normalized tower datum of [def-pur-tate-datum]. Continue the tower notation of Step 6 and put $a=H(\phi)b_K$, $c=G(\phi)e_K$. Naturality of $\gamma$ in [det-sp-tower-gamma] and Step 6 give the purity equation
$$c\,Q\gamma_K=G(\phi)\gamma_{PK}b_K=\gamma_KH(\phi)b_K=\gamma_Ka.$$
This is an equality of derived tower morphisms.

Cited nodes: def-pur-tate-datum, det-sp-tower-gamma.

### Returned step 8

For a tower datum $\varphi_M:QM\to M$, write $\varphi_{FM}=F(\varphi_M)B_M$, the transport formula of [def-pur-compact-support-transport] applied to the compatible tower data of [def-pur-tate-datum]. The adjunct-counit identity [lem-weil-pbc-adjunct-counit-identity] applied to the transpose defining $e$ in [det-sp-tower-exceptional-bc] gives $\varepsilon_{PK}F(e_K)=P(\varepsilon_K)B_{GK}^{-1}$. Counit naturality therefore gives
$$\varepsilon_K\varphi_{FGK}=\varepsilon_KF(G(\phi))F(e_K)B_{GK}=\phi\varepsilon_{PK}F(e_K)B_{GK}=\phi P(\varepsilon_K).$$
Thus the tower exceptional counit is equivariant.

Cited nodes: def-pur-compact-support-transport, def-pur-tate-datum, lem-weil-pbc-adjunct-counit-identity, det-sp-tower-exceptional-bc.

### Returned step 9

Naturality of the tower exchange $B$ of [det-sp-tower-exceptional-bc] at $\gamma_K$, followed by Step 7, gives
$$F(\gamma_K)\varphi_{FHK}=F(\gamma_Ka)B_{HK}=F(c)FQ(\gamma_K)B_{HK}=F(c)B_{GK}PF(\gamma_K)=\varphi_{FGK}PF(\gamma_K).$$
Postcompose with $\varepsilon_K$ and substitute Step 8. For the tower trace $t_K=\varepsilon_KF(\gamma_K)$ this yields $t_K\varphi_{FHK}=\phi P(t_K)$. The three tower equations are those of Steps 7–9. None is inferred from equality of finite evaluations.

Cited nodes: det-sp-tower-exceptional-bc.

### Returned step 10

Apply the functor $R\varprojlim$ to the three equalities of Steps 7–9. The unit assertion of [det-sp-normalized-equivalence] says that $K\to R\varprojlim\operatorname{red}_YK$ is an isomorphism for every derived-complete $K$, so it identifies the input tower with the integral object. Only this derived-complete unit assertion is used here, not the separately stated Noetherian constructible-equivalence clause. By [det-sp-integral-adjunction-bijection], the integral purity map and the integral unit and counit are the realized tower maps, and [det-sp-integral-direct-image-tower] identifies $F$ with the realized tower compact-support functor. The horizontal maps are isomorphisms: their inverse-image equivalences [lem-weil-proetale-isomorphism-inverse-image], identified with derived pullback by [lem-weil-isomorphism-derived-pullback], commute with this realization. Indeed the exact inverse-image equivalence on each site induces an exact equivalence on strict towers (and on modules over the completed ring identified by the inverse-limit coefficient comparison). It preserves K-injective complexes: for an acyclic test complex, the Hom complex after applying the equivalence identifies with the Hom complex from its acyclic inverse image. It also commutes with ordinary inverse limit, so computing total derived inverse limit on these K-injective resolutions identifies its conjugate with the same derived functor. These identifications give the integral $P,Q,B,e,b$ and the data in the statement. Realization preserves composition and equalities; hence all three equations hold over $\mathcal O_E$. This uses a functor on coherent towers, not faithfulness of the collection of finite reductions.

Cited nodes: det-sp-normalized-equivalence, det-sp-integral-adjunction-bijection, det-sp-integral-direct-image-tower, lem-weil-proetale-isomorphism-inverse-image, lem-weil-isomorphism-derived-pullback.

### Returned step 11

For $\Lambda=E$, the strict datum is obtained from an integral datum by [def-pur-tate-datum]. Apply the rationalization functor to the equalities of Step 10. The purity and trace maps are their transported maps by [thm-pur-rational-and-qbar-purity, prop-pur-rational-purity-trace-coherence]; their composites and exchange maps are the transported composites specified in [def-exchange-projection]. Functors preserve the displayed equalities. For $\Lambda=\overline{\mathbf Q}_\ell$, choose a common finite coefficient field representing the datum as in [def-pur-tate-datum] and use the same argument there, then take its common-stage morphism class. The rational trace-coherence statement supplies compatibility with the coefficient extension; a further finite extension sends the same equality to an equality. This proves the asserted squares at all four coefficient stages.

Cited nodes: def-pur-tate-datum, thm-pur-rational-and-qbar-purity, prop-pur-rational-purity-trace-coherence, def-exchange-projection.

## Unfinished work

The three new comparison nodes are deliberately unsplit, for separate workers. No requested repair point is left outstanding. Delivery checks are run on the server using the required delivery command.
