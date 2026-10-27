# Stage-1 re-split: det-sp-purity-bc-factors

## Files written

- dag/nodes/sec-smooth-purity/det-sp-purity-bc-factors.json: item, split; original statement and statement dependencies unchanged; five assembly steps, 2131 characters.
- dag/nodes/sec-smooth-purity/lem-sp-diagonal-exchange-cube.json: statement, unsplit; no Mathlib match for the counit-defined cube and diagonal comparison.
- dag/nodes/sec-smooth-purity/lem-sp-section-dnc-integration-square.json: statement, unsplit; no Mathlib match for the integrated normalized section-deformation square.
- dag/nodes/sec-smooth-purity/lem-sp-orientation-scalar-tower-transport.json: statement, unsplit; no Mathlib match for the two coefficient transport interfaces. Single-complex faithfulness is an existing ingredient, not the whole statement.
- dag/nodes/sec-smooth-purity/lem-sp-proetale-ctf-pullback-domains.json: statement, unsplit; no Mathlib match for arbitrary finite-ring intrinsic pro-etale constructibility/Tor bounds and non-normalized uniform towers.
- dag/nodes/sec-smooth-purity/lem-sp-tensor-counit-exchange-calculus.json: statement, unsplit; no Mathlib match for the two-adjunction projection/exchange tensor-counit calculation.
- report.md and citations.json: self-review and verbatim statement quotations for all 18 assembly citations. searches.jsonl and the per-node search-result files preserve the real search responses. Auxiliary Python/JSON files are sandbox-only working material.

## Attachments

None. I searched WeilConjectures for the item tag and for purity/base-change, diagonal, tensor, exchange and projection terms. In EtaleCohomology/Purity/Smooth/Basic.lean, AlgebraicGeometry.Etale.leftDerivedUpperStar_map_comp_smoothPullbackExchange_hom (line 374) proves a square for smoothPullbackExchange (line 338), which is defined by conjugating chosen purity isomorphisms. It does not identify the independently counit-defined exceptional exchange, nor does it give the orientation and tensor clauses for arbitrary finite rings and ordinary coefficient towers. The diagonal-orientation existence theorem in that file still has sorry (line 211). The closed projection/base-change declarations in LowerShriekProjectionBaseChange.lean support an existing compact-projection node, not an attachment of this whole item or any new interface.

## WANTED

None: the new interfaces are explicitly agent-extracted from the available current blueprint and the previously reviewed expanded proof. No missing document is claimed to contain these exact new statements.

## What was wrong and what changed

The released stage-1 repair record dated 2026-10-22 explicitly reopens the reviewed node, preserves its statement/plan, requires at least four independently assignable nodes, and caps the assembly at 3000 characters. The previous review is retained as metadata/history; it does not override this order. This delivery adds five new statement-only nodes of comparable size and keeps the diagonal, deformation, vector-integration, coefficient, ordinary-tower and adjoint-transpose route. This is a finer split of existing work, not a statement dispute.

No imported hypothesis or conclusion was altered. The finite coefficient domain still permits every finite commutative ell-primary ring, the base change need not be flat, E may be ramified, and input towers need not be normalized. Every newly exposed assertion is an interface for an intermediate argument, not the full item or an unqualified copy of one of its clauses. The scalar/tower node is conditional on the base-ring orientation square; the section node is for a general closed smooth section and does not compare the diagonal-to-dualizing arrow; the cube node has no orientation. The tensor node is an abstract conditional implication from projection/exchange coherence, not the geometric tensor clause by itself.

The preserved-work map is:

1. Old step 1 goes to lem-sp-diagonal-exchange-cube: the pullback identification of the diagonal pair, smooth/closed-section hypotheses, witnessed finite domains, exact cube equation, and the resulting kappa equation. Its full pasting argument is retained verbatim below.
2. Old step 2 goes to lem-sp-section-dnc-integration-square: the actual normal bundle, fibers, non-flat closed-section DNC base change, integration normalization and its square; the diagonal composite is identified with the specified orientation. Assembly step 1 combines this with the cube equation.
3. Old steps 3 and 4 go to lem-sp-orientation-scalar-tower-transport: finite scalar cancellation and equality of equally shifted tower-sheaf morphisms. The existing mixed coefficient square remains an explicit assembly citation. Neither the new statement nor its intended proof assumes faithful evaluation of arbitrary derived morphisms.
4. Old step 5 remains a use of the existing lem-sp-compact-projection-base-change, whose statement already includes the inverse formula, with its invertibility checks made in assembly step 3. The finite maps are compactification composites over the constant ring A; tower maps are formed in the inverse-system topos, not lifted from equality of evaluations. No duplicate projection lemma is created.
5. Old step 6 goes to lem-sp-proetale-ctf-pullback-domains: bounded flat representatives, K-flatness, termwise exact pullback, pulled-back finite strata and local models, derived tensor interval, cohomology constructibility, uniform tower bounds, ramification indexing, and the allowed tensor-source domain.
6. Old step 7 goes to lem-sp-tensor-counit-exchange-calculus. It isolates the actual two-transpose calculation, with the correct counit mate and the inverse-projection square as hypotheses. It does not strengthen a projection hypothesis to all objects: invertibility is required only at the three displayed pairs. The seven-line computation is retained below for the future worker.
7. Old step 8 is the short final assembly step: substitution into gamma=t(1 tensor a)tau, in the ordinary derived category and then its full subcategory. The inherited reassociation justification and all original citations remain in the verbatim appendix.

Each new node's source.place points to its exact old-step appendix and identifies the interface as agent-extracted. This retains the detailed arguments in the delivery while complying with the instruction that new unsplit nodes themselves carry statements only.

## Not duplicates

lem-sp-diagonal-exchange-cube vs lem-pur-diagonal-base-change: the latter gives C(p1,Delta) isomorphic to omega_f for one map, but does not give the counit-defined base-change cube or the kappa/e equation.
lem-sp-diagonal-exchange-cube vs lem-pur-diagonal-section-pasting: that node treats composition of two smooth maps and the sigma/kappa tensor-pasting identity, not arbitrary base change of one diagonal pair.
lem-sp-diagonal-exchange-cube vs lem-pur-smooth-exceptional-tensor-pasting: general exceptional pasting is an ingredient, while the new node specifies the diagonal cube, chosen kappa, witnessed domains and their precise equality.
lem-sp-section-dnc-integration-square vs thm-pur-dnc-invariance: the latter supplies the normalized DNC arrow, without the subsequent actual zero-section integration comparison and identification of the diagonal composite.
lem-sp-section-dnc-integration-square vs cor-pur-vector-bundle-purity: that node treats a vector-bundle projection, not a general smooth closed-section deformation and its two fiber comparisons.
lem-sp-section-dnc-integration-square vs lem-pur-diagonal-orientation-refinement: that node is compatibility under inclusion of affine target opens; the new node treats arbitrary base change of a smooth section pair.
lem-sp-section-dnc-integration-square vs lem-trf-ambient-diagonal-purity-base-change: the latter is a whole ordinary-etale ambient duality theorem at residue rings; the new node concerns the pro-etale constructible section invariant and the intermediate DNC/integration composite, before diagonal comparison.
lem-sp-orientation-scalar-tower-transport vs lem-pur-dnc-coefficient-transport: mixed coefficient/exchange compatibility is an input to clause (1), not the conclusion of scalar orientation cancellation or shifted tower-map equality.
lem-sp-orientation-scalar-tower-transport vs lem-weil-pbc-derived-single-fully-faithful: this Mathlib leaf is used inside clause (2), but does not supply exact varying-ring tower evaluation, the shift removal, or scalar-orientation transport.
lem-sp-orientation-scalar-tower-transport vs lem-pur-system-derived-evaluation: detecting isomorphisms and cohomological bounds of system objects does not assert injectivity on the Hom sets between equally shifted sheaf towers.
lem-sp-proetale-ctf-pullback-domains vs lem-sf-pullback-tor-amplitude: that node is for the residue ring A_{E,n}; the new interface covers every finite ell-primary ring on the intrinsic pro-etale category and includes non-normalized ordinary tower domains.
lem-sp-proetale-ctf-pullback-domains vs lem-sp-etale-pullback-line-flat-model: that node is on the ordinary etale site with a supplied bounded flat representative and an additional line tensor; the new node includes intrinsic pro-etale representatives and whole varying-coefficient towers.
lem-sp-proetale-ctf-pullback-domains vs lem-sp-etale-pullback-twist-tor-window: etale flat models at a finite ring do not themselves identify the intrinsic pro-etale domains and uniformly bounded tower adjunction inputs.
lem-sp-tensor-counit-exchange-calculus vs lem-pur-integration-transpose-base-change: that node is geometric ordinary etale integration for a pair of trace objects; the new statement is the abstract two-adjunction tensor-counit calculation applicable in the inverse-system topos as well.
lem-sp-tensor-counit-exchange-calculus vs lem-pur-smooth-exceptional-tensor-pasting: that node fixes residue-ring smooth pro-etale morphisms and asserts many composition compatibilities; the new node is a conditional categorical lemma independent of smoothness and coefficient categories.
lem-sp-tensor-counit-exchange-calculus vs lem-pur-ordered-tensor-coefficient-mate: its scalar projection/evaluation comparison is a different diagram, and does not assert compatibility of exceptional adjoint transposes under a counit-defined base-change mate.
lem-sp-tensor-counit-exchange-calculus vs lem-asd-adjunction-projection-map-mate: that lemma transports left-adjoint projection maps from unit-defined right-adjoint comparisons; the new node transports right-adjoint tensor maps from inverse projection and counits.
lem-sp-tensor-counit-exchange-calculus vs lem-pur-system-tensor-transpose-composition: that node concerns composition of two morphisms on normalized coherent systems, not a base-change mate between two adjunctions on possibly non-normalized ordinary towers.

I searched the whole DAG by concept and read the above candidate statements, and searched all blueprint nodes with blueprint_refs.py (diagonal, section invariant, orientation, finite Tor, constructible finite, transpose, counit and narrower combinations). No existing node states any whole new interface. The five new source citations are to the blueprint factor proof rather than to a Stacks tag: they are extracted interfaces, not assertions falsely attributed to Stacks. The reused compact-projection lemma carries the Stacks 0E48/07A4 content. Definitions used to state each node are explicit statement dependencies.

## Review by Q115

I read the current main-20261015 sk-prop-sp-purity-bc unit, factor statement and factor proof, the live expanded eight-step argument, and the released repair note. I compared every hypothesis against the unchanged statement: the field and coefficient data, separated finite-type schemes, smooth pure-dimensional f, arbitrary v, the finite ring or actual ordinary tower category, and the transpose definition of e. The chapter route stays through the diagonal and closed-section deformation. I also read Stacks sites-cohomology.tex, remark-compatible-with-diagram (0E48), including its explicit arrow conventions, and its pullback-tensor lemma locator (07A4). I used those only through the existing compact-projection interface, never as a replacement SGA trace route.

For the cube statement I opened lem-pur-diagonal-base-change, fix-lem-exchanges, lem-weil-pbc-mate-pasting, lem-sbc-smooth-relative-dimension-permanence, lem-pur-diagonal-regular-immersion and det-pe-finite-tor-comparison-noetherian. They provide respectively the chosen comparison, compact-support pasting, pasting of the inverse-exchange mates, preservation of d, the closed regular diagonal, and etale-origin witnesses. The nontrivial kappa/e compatibility is the new conclusion, not something falsely taken from the existence-only diagonal node. I checked p2 Delta=1 and q Delta'=Delta u, and that the two paths in the cube have the same source q^*p2^*omega_f and target omega_p1'. Finite R is discrete Noetherian; all schemes here are qcqs. In step 1 the new section-square statement takes exactly Delta'^*b_p1 as its section comparison, so its composite with the new cube equation proves the required residue orientation equation without an unspecified isomorphism.

For the general section statement I read thm-pur-dnc-invariance, lem-pur-dnc-section-geometry, cor-pur-vector-bundle-purity and det-sp-orientation-charts. The first two require a smooth morphism with a closed section, which p1 and Delta satisfy. Their arbitrary base-change assertions apply along u without flatness. The vector arrow is the integration-normalized comparison and its zero-section pullback; chart normalization identifies the composite with the diagonal orientation. The statement specifies the whole intermediate square and exact normal bundle, so a future worker has the correct comparison to prove.

For assembly step 2 I opened det-sp-finite-general-ring and lem-pur-dnc-coefficient-transport: the former says Pi_A c_f=(Pi_R)_A, and the latter explicitly states e_A u^*c_f=c_f' (e_R)_A. These are the two hypotheses of new scalar transport (1), which the inherited cancellation calculation proves. I then checked det-sp-tower-gamma and det-sp-tower-exceptional-bc really supply actual tower morphisms and exactly the indicated finite evaluations. For transport (2), det-sp-coefficient-towers-abelian supplies exact evaluation and the abelian category, sk-def-sp-coefficient-towers supplies componentwise morphisms, and lem-weil-pbc-derived-single-fully-faithful supplies full faithfulness. I read Mathlib Algebra/Homology/DerivedCategory/FullyFaithful.lean, lines 29-60: this is an ingredient, not a claim that derived evaluations are faithful in general. The tower-line shift removal is legitimate because both line objects are shifted sheaf towers with the same shift. Ramified ell^n levels are uniformizer levels en; no quotient flatness is used.

For assembly step 3 and the domain statement I read sk-lem-sf-flat-model, lem-pc-bounded-above-flat-kflat-site, lem-weil-pbc-ringed-pullback-preserves-kflat, def-weil-pbc-proetale-operations, def-weil-proetale-constructible-sheaf, lem-sf-pullback-tor-amplitude, sk-def-sp-normalized-towers and det-sp-tower-gluing. Their statements give the exact bounded flat models, K-flat computations, inverse-image exactness and tower Hom domains needed. I checked the finite-A argument preserves the representative degree interval; tensoring with a sheaf then has no terms outside it. Pullback of the finite stratification and its local finite models proves constructibility, while exactness gives cohomology pullback. Tower common cohomological bounds follow from exact levelwise pullback and common Tor bounds from the finite residue statement. The oriented tensor objects differ by the actual e1 and monoidal comparison, not merely by an equality of their levels.

I read the full statement of lem-sp-compact-projection-base-change. It asserts the displayed inverse equation when the four maps are invertible, at both finite A and ordinary towers. det-sp-finite-general-ring(3), det-sp-tower-gamma(2), the orientation identity already established, naturality and the stated exchanges provide exactly those invertibilities at M=omega_f. The equation is in the ambient derived category, so it is usable without faithful evaluation. This checks the C4 risk in step 3: its cited statement really contains its inverse equation, not just the proper projection version.

For assembly step 4 I checked the abstract statement against every line of inherited step 7. The first equality is the defining counit transpose, the second beta naturality, the third the tensor-map transpose, the fourth inverse projection compatibility, the fifth the same counit identity at the unit, and the sixth projection naturality at e1. The new statement records the common final adjunct, so the Hom-bijection injectivity has an exact conclusion to apply. I corrected an initial draft that asked for projection isomorphisms everywhere: the final draft asks for invertibility only at (K,G1), (VK,UG1), (VK,G'1). This matters because the assembly verifies only these points. I also explicitly allowed restricted adjunctions inside ambient monoidal categories. The available Mathlib monoidal-adjunction counit tensor identities (Monoidal/Functor.lean, lines 1024-1040) concern one monoidal adjunction; they do not give this two-adjunction exchange/projection implication in one specialization.

For assembly step 5 I re-opened def-pur-smooth-purity-map, det-sp-finite-general-ring(3) and det-sp-tower-gamma(2). All three define the same inverse-orientation-then-tensor composite on their respective domains. The final substitution is elementary functoriality and bifunctoriality under the canonical twist reassociations already fixed in the statement. The inherited tensor/pullback comparison justification is retained below. No new lemma restates gamma compatibility.

I checked delivery-errors B-E against the actual files. New nodes are self-contained statements with no proof list, no hidden normalization hypothesis, real definition dependencies and blueprint ancestry. The source locations distinguish agent extraction from quotation. All search records came from msearch.py; the unknown-name Loogle query for pullback was retained honestly and followed by a valid SheafOfModules.pullback query. I inspected every returned name/signature: scheme smoothness/normalization, module dual base change, cochain shifts, Mayer-Vietoris, monoidal unit/counit and ordinary module pullback are not the whole interfaces. The exact searches and results are preserved, with a second semantic phrasing for each node. No Mathlib leaf is falsely claimed.

Small cases checked: identity v reduces the cube and all scalar squares to identities; d=0 uses rank-zero normal bundles and no coordinate factors; empty schemes give the zero-category identities; the zero finite ring gives zero objects; a non-flat closed base change is still a smooth closed-section DNC base change; a ramified E uses en rather than n; and a non-normalized sheaf tower still has componentwise maps and exact evaluations. In the abstract counit lemma I checked the identity-adjunction/unit case and the source/target of every composite; no invertibility of e1 is needed there. All assembly steps are below 2000 characters, all non-elementary uses are citations, and proof_deps is precisely their union. The five new tasks distribute the original work; their statements range from roughly 2.1k to 3.4k characters and none carries the whole theorem.

No second worker was started: this is the direct-delivery self-review required by the dispatched brief. The maintainer provides the independent review after delivery.

## What remains unfinished

The five new nodes are intentionally unsplit stage-1 tasks, not proved Lean results. No Lean was written, compiled or built. Their intended proof material is fully retained below, so their future workers do not need to reconstruct the old argument from memory. The assembly itself is complete relative to these statements and the existing cited nodes.

## Appendix: inherited argument

The following is the complete previously reviewed eight-step proof, preserved verbatim (including its original node citations). These are proof instructions for the new tasks or the stated reuse, not proof fields of the statement-only nodes.

### Old step 1

First take $R=\mathbf Z/\ell^r$, $r\geq1$. Write $W=X\times_YX$, $p_1,p_2:W\to X$ and $\Delta:X\to W$. In the analogous primed diagram, $W'$ with its projection $p_1'$ and section $\Delta'$ is the pullback of $(W,p_1,\Delta)$ along $u:X'\to X$: both fibre products represent pairs of points of $X$ over the same point of $Y$, together with a lift of that point to $Y'$. The identities $p_2\Delta=1$ and $p_2'\Delta'=1$ are preserved. Let $\kappa_f:C(p_1,\Delta)\xrightarrow{\sim}\omega_{f,R}$ be the comparison in [lem-pur-diagonal-base-change]. Its pullback comparison is the one obtained from $e_1$ for $f$ and the exceptional comparison for $p_1$. Indeed [fix-lem-exchanges](2) says that compact-support exchanges respect horizontal and vertical pasting at these finite coefficients. The corresponding compact-support squares paste to the same square; applying [lem-weil-pbc-mate-pasting](1)-(2) to their inverse compact-support exchanges gives the same exceptional comparison, and the identity square has identity mate by clause (4). Thus the $C$-to-$\omega$ identification respects these specified, counit-defined exchanges, rather than an unspecified isomorphism. The smooth and pure-relative-dimension hypotheses for $p_1,p_1'$ follow from [lem-sbc-smooth-relative-dimension-permanence](1). The diagonal is a closed section because $f$ is separated, as asserted in [lem-pur-diagonal-regular-immersion]. More explicitly, put $q:W'\to W$, let $b_f:p_2^*\omega_f\to\omega_{p_1}$ be the exceptional exchange in the diagonal square, and let $b_{p_1}:q^*\omega_{p_1}\to\omega_{p_1'}$ be the exchange along $u$. The two pasted-square expressions give
$$b_{p_1}\,q^*b_f=b_{f'}\,p_2'^*e_1.$$
Since $\kappa_f=\Delta^*b_f^{-1}$ and $p_2'\Delta'=1$, pulling this equation back along $\Delta'$ and rearranging gives
$$\kappa_{f'}\,\Delta'^*b_{p_1}=e_1\,u^*\kappa_f,$$
which is the required compatibility for the first arrow of the orientation construction. The witnessed finite pro-etale domain required by [fix-lem-exchanges] is available: [det-pe-finite-tor-comparison-noetherian] gives an etale constructible finite-Tor representative for each constructible finite-Tor object used here. Its scheme hypothesis holds because our separated finite-type $k$-schemes are quasi-compact and quasi-separated; its coefficient hypothesis holds because $R$ is finite and hence discrete Noetherian. Choose such witnesses before applying exchange pasting.

Uses: lem-pur-diagonal-base-change, lem-weil-pbc-mate-pasting, lem-sbc-smooth-relative-dimension-permanence, lem-pur-diagonal-regular-immersion, fix-lem-exchanges, det-pe-finite-tor-comparison-noetherian.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/_section.md; Orientation paragraph: base-changed diagonal and the specified exceptional exchange.

### Old step 2

For this smooth closed-section pair, let $N=N_{\Delta/W}$, with projection $\pi_N$ and zero section $z$, and let $\delta:C(p_1,\Delta)\xrightarrow{\sim}C(\pi_N,z)$ be [thm-pur-dnc-invariance]. By [lem-pur-dnc-section-geometry](1),(5), the deformation family and its fibres commute with the arbitrary base change $u$; taking the fibre at $0$ identifies the primed normal-bundle pair with the pullback of $(N,z)$. The rank is $d$ by [lem-pur-diagonal-regular-immersion]. Write $b_N:\omega_{\pi_N}\xrightarrow{\sim}R_N(d)[2d]$ for vector-bundle purity. By [cor-pur-vector-bundle-purity], $b_N$ commutes with base change and with the adjunction comparisons. The diagonal orientation is the composite
$$\Pi_{f,R}:\omega_{f,R}\xrightarrow{\kappa_f^{-1}}C(p_1,\Delta)\xrightarrow{\delta}z^*\omega_{\pi_N}\xrightarrow{z^*b_N}R_X(d)[2d].$$
This spells out the canonical diagonal construction of [thm-pur-diagonal-dualizing-object]; its chart normalization is exactly [det-sp-orientation-charts]. The first arrow respects the exchange by step 1, the second by the arbitrary-base-change assertion of [thm-pur-dnc-invariance], and the third by vector-bundle purity. Pullback of the displayed three-arrow composite is therefore its primed composite, so $\Pi_{f',R}e_{1,R}=u_R^*\Pi_{f,R}$. Taking inverses gives $e_{1,R}u_R^*a_{f,R}=a_{f',R}$. Here $u$ need not be flat: DNC base change is used only for a smooth morphism with a closed section, precisely the hypothesis of the cited geometry and invariance statements.

Uses: thm-pur-dnc-invariance, lem-pur-dnc-section-geometry, lem-pur-diagonal-regular-immersion, cor-pur-vector-bundle-purity, thm-pur-diagonal-dualizing-object, det-sp-orientation-charts.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/_section.md; Orientation paragraph: deformation, normal bundle, vector-bundle integration, and coordinate normalization.

### Old step 3

Let $A$ be any finite commutative ring with $\ell^rA=0$, and write $(-)_A=-\otimes_R^LA$. By [det-sp-finite-general-ring](1)-(2), its diagonal orientation is characterized by $\Pi_{f,A}c_f=(\Pi_{f,R})_A$, where $c_f:(\omega_{f,R})_A\xrightarrow{\sim}\omega_{f,A}$. The mixed exchange identity of [lem-pur-dnc-coefficient-transport], applied to $f$ and $v$, is $e_{1,A}u_A^*c_f=c_{f'}(e_{1,R})_A$. Canonical pullback/tensor comparisons are supplied by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Hence
$$\Pi_{f',A}e_{1,A}u_A^*c_f=\Pi_{f',A}c_{f'}(e_{1,R})_A=(\Pi_{f',R}e_{1,R})_A=(u_R^*\Pi_{f,R})_A=(u_A^*\Pi_{f,A})(u_A^*c_f).$$
Cancel the isomorphism $u_A^*c_f$. Inverting the resulting equation proves clause (1) for $A$. This includes $A_n=\mathcal O_E/\ell^n$: if $\ell$ is a unit times $\varpi_E^e$, this is $A_{E,en}$, with no unramifiedness assumption. Twist identifications here are the exponent-independent ones in [det-sp-finite-general-ring].

Uses: det-sp-finite-general-ring, lem-pur-dnc-coefficient-transport, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/_section.md; Orientation paragraph: the finite-level calculation with general finite coefficients.

### Old step 4

For towers, [det-sp-tower-gamma](1) supplies actual orientation morphisms $a_f,a_{f'}$ in the ordinary tower derived categories, and [det-sp-tower-exceptional-bc](2) supplies an actual $e_1$ evaluating to the finite exceptional maps. Put $L=A_{\bullet,X'}(d)[2d]$ and $h=a_{f'}^{-1}e_1u_\bullet^*a_f\in\operatorname{End}(L)$. Step 3 says $h_n=1$ at every $n$. The twists before shifting are towers of sheaves by [def-coefficient-twists-detailed, sk-def-sp-coefficient-towers]. Remove $[2d]$. Since $\operatorname{Tow}$ is abelian and evaluation is exact [det-sp-coefficient-towers-abelian](1)-(2), full faithfulness of the single-complex embedding [lem-weil-pbc-derived-single-fully-faithful] identifies $h$ with a unique endomorphism of the sheaf tower $A_{\bullet,X'}(d)$. Its $n$th sheaf component is the identity by the same full faithfulness at finite level. Morphisms of towers are componentwise families [sk-def-sp-coefficient-towers], so this endomorphism is the identity. Consequently $h=1$ and $e_1u_\bullet^*a_f=a_{f'}$. This proves tower clause (1) without claiming faithfulness of evaluation on arbitrary derived morphisms.

Uses: det-sp-tower-gamma, det-sp-tower-exceptional-bc, def-coefficient-twists-detailed, sk-def-sp-coefficient-towers, det-sp-coefficient-towers-abelian, lem-weil-pbc-derived-single-fully-faithful.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/_section.md; Orientation paragraph: equality between shifted tower sheaves, tested at each level.

### Old step 5

We use the projection/base-change compatibility [lem-sp-compact-projection-base-change] for the compactification $f=pj$ and its pullback, in its setting (i) for finite $A$ and in its setting (ii) for towers. Its maps are the ones occurring in this proof. At finite coefficients its exchange $\beta$ and projection map are the compactification composites of [def-exchange-projection], formed with the constant ring $A$ in place of the residue ring (the same defining formulas with ordinary constant-$A$ ringed-module adjunctions; no residue-ring-only theorem is applied to $A$). For towers they are the levelwise-formed compactification projection and exchange maps of [det-sp-tower-shriek-levels](2), and the exchange is $\beta_{f,\bullet}$ of [det-sp-tower-exceptional-bc](1). Write $q_f(K,M):F_f(f^*K\otimes M)\to K\otimes F_fM$ for the inverse projection formula, with tensor symmetry understood. Take $M=\omega_f$. The projection map of $f$ at $(\omega_f,K)$ is invertible by the finite tensor-map construction [det-sp-finite-general-ring](3) or the tower construction [det-sp-tower-gamma](2); the projection map of $f'$ at $(u^*\omega_f,v^*K)$ is invertible because it corresponds, by naturality in its first argument and the isomorphism $e_1:u^*\omega_f\to\omega_{f'}$ of clause (1), to the projection map at $(\omega_{f'},v^*K)$, invertible by the same constructions for $f'$. The exchanges $\beta_{\omega_f}$ and $\beta_{f^*K\otimes\omega_f}$ are invertible by compact-support base change (finite coefficients) and [det-sp-tower-exceptional-bc](1) (towers; the objects lie in the constructible finite-Tor category by step 6 and [det-sp-tower-gamma](2)). The inverse form of [lem-sp-compact-projection-base-change] then gives
$$(v^*K\otimes\beta_{\omega_f})\,v^*q_f(K,\omega_f)\,\beta_{f^*K\otimes\omega_f}^{-1}=q_{f'}(v^*K,u^*\omega_f).$$
For towers this is an identity in the tower derived category itself, not inferred from equality of finite derived evaluations.

Uses: lem-sp-compact-projection-base-change, def-exchange-projection, det-sp-tower-shriek-levels, det-sp-tower-exceptional-bc, det-sp-finite-general-ring, det-sp-tower-gamma.

Source: literature/stacks-project/sites-cohomology.tex; Tags 0E48 (remark-compatible-with-diagram), 07A4 (lemma-pullback-tensor-product); compactification composition and the explicit open-adjunction check above.

### Old step 6

All transposes in the following calculation are on their stated constructible finite-Tor domains. For tower $K$ with common Tor interval $[a,b]$, pullback $v^*K$ has the same bounds by [lem-sf-pullback-tor-amplitude] applied at $A_n=A_{E,en}$, since exact levelwise pullback preserves the cohomological interval. The same node supplies constructibility at each level; the definition [sk-def-sp-normalized-towers] therefore puts $v^*K$ in the uniform category. The source $f'^*v^*K\otimes\omega_{f'}$ belongs to it by [det-sp-tower-gamma](2), and $u^*(f^*K\otimes\omega_f)$ is isomorphic to this source by clause (1) and the monoidal comparison. Thus the tower adjunction [det-sp-tower-gluing] applies. For general finite $A$, use [sk-lem-sf-flat-model] to represent $K$ by a bounded complex $P$ of flat constructible $A_Y$-sheaves. It is K-flat by [lem-pc-bounded-above-flat-kflat-site], and [lem-weil-pbc-ringed-pullback-preserves-kflat] says that $v^*P$ has flat terms and is K-flat. Exact constant-coefficient inverse image is the termwise computation of $Lv^*$ [def-weil-pbc-proetale-operations], so it preserves the finite degree interval of $P$. The terms of $v^*P$ are constructible: pull the finite stratification for each term back along $v$, intersect these finitely many partitions, and pull the locally constant finite local models back on each stratum, exactly the condition of [def-weil-proetale-constructible-sheaf]. For every sheaf $N$ in degree zero the tensor $v^*P\otimes N$ has terms only in that same finite interval, and hence zero cohomology outside it; the K-flat computation makes this the required derived tensor. Thus $v^*K$ has finite Tor amplitude. To check constructible cohomology as well, apply the same pulled-back stratification argument to the finitely many constructible cohomology sheaves of $K$; exactness gives $\mathcal H^i(v^*K)=v^*\mathcal H^i(K)$. This puts $v^*K$ in the finite category of [det-sp-finite-general-ring]. Its oriented tensor source is a twisted shift of its pullback, so is an allowed input for the stated adjunction and tensor map. No normalization of towers or flatness of the quotient $A_n\to A_m$ is used.

Uses: lem-sf-pullback-tor-amplitude, sk-def-sp-normalized-towers, det-sp-tower-gamma, det-sp-tower-gluing, sk-lem-sf-flat-model, lem-pc-bounded-above-flat-kflat-site, lem-weil-pbc-ringed-pullback-preserves-kflat, def-weil-pbc-proetale-operations, def-weil-proetale-constructible-sheaf, det-sp-finite-general-ring.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/_section.md; Tensor-map paragraph: domains of the finite and tower adjunctions.

### Old step 7

Write $F=F_f$, $F'=F_{f'}$, $G=G_f$, $G'=G_{f'}$, suppress the coefficient index, and put $P=f^*K\otimes\omega_f$, $K'=v^*K$. By the defining transpose of $e_K$ (finite: [def-pur-co-smoothness] for its unit component and [def-weil-pbc-adjunction-mate] for the general counit mate; tower: [det-sp-tower-exceptional-bc](2)),
$$\varepsilon'_{K'}F'(e_K)=v^*\varepsilon_K\,\beta_{GK}^{-1}.$$
The tensor maps are the transposes of $(1\otimes\varepsilon_1)q_f(K,\omega_f)$ by [def-pur-co-smoothness, det-sp-finite-general-ring, det-sp-tower-gamma]. Using naturality of $\beta$, then this defining transpose, then step 5 gives
$$\begin{aligned}
\varepsilon'_{K'}F'(e_Ku^*t_{f,K})
&=v^*\varepsilon_K\,\beta_{GK}^{-1}F'u^*t_{f,K}\\
&=v^*(\varepsilon_KF t_{f,K})\,\beta_P^{-1}\\
&=v^*((1\otimes\varepsilon_1)q_f(K,\omega_f))\,\beta_P^{-1}\\
&=(1\otimes(v^*\varepsilon_1\,\beta_{\omega_f}^{-1}))\,q_{f'}(K',u^*\omega_f)\\
&=(1\otimes(\varepsilon'_1F'e_1))\,q_{f'}(K',u^*\omega_f)\\
&=(1\otimes\varepsilon'_1)q_{f'}(K',\omega_{f'})F'(1\otimes e_1)\\
&=\varepsilon'_{K'}F'\bigl(t_{f',K'}(1\otimes e_1)\bigr).
\end{aligned}$$
The fifth line is the same counit identity at the unit; the sixth is naturality of projection formula in its second input. By injectivity of the adjunction Hom bijection, the first and last maps have equal transposes and are equal. This proves clause (2) simultaneously at finite coefficients and in the tower derived category.

Uses: def-pur-co-smoothness, def-weil-pbc-adjunction-mate, det-sp-tower-exceptional-bc, det-sp-finite-general-ring, det-sp-tower-gamma, det-sp-tower-gluing.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/_section.md; Tensor-map paragraph: counit calculation with the two transposes written explicitly.

### Old step 8

By [def-pur-smooth-purity-map] for the residue-ring coefficients, [det-sp-finite-general-ring](3) for general finite $A$, and [det-sp-tower-gamma](2) for towers, $\gamma_f=t_{f,K}(1\otimes a_f)\tau$, with $\tau$ the canonical twist/shift reassociation. Pullback respects this reassociation by the monoidal comparison [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] and the finite twist comparisons in [det-sp-finite-general-ring]. Substituting the two clauses just proved gives
$$e_Ku^*\gamma_f=t_{f',v^*K}(1\otimes e_1)(1\otimes u^*a_f)\tau'=t_{f',v^*K}(1\otimes a_{f'})\tau'=\gamma_{f'}(v^*K).$$
At tower coefficients all maps in this equality were constructed in the same ordinary derived category; it is an equality there and hence in its full constructible finite-Tor subcategory.

Uses: def-pur-smooth-purity-map, det-sp-finite-general-ring, det-sp-tower-gamma, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/_section.md; Last assertion: compose orientation, tensor map, and twist reassociation.
