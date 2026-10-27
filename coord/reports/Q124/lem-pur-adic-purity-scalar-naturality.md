# Stage-1 delivery: Q124

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-adic-purity-scalar-naturality.json`: unchanged statement and statement dependencies; four-step assembly.
- `dag/nodes/sec-smooth-purity/lem-pur-adic-operation-domains-source-comparison.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-adic-unit-trace-transpose-reductions.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-adic-trace-transpose-coefficient-calculus.json`: statement, unsplit; no Mathlib match.

## Attachments

None. The project search by blueprint tag and scalar/purity terminology found no declaration supplying the simultaneous integral family. Smooth/Adic.lean explicitly assumes its normalized systems and their coherent level maps; its reconstruction-only theorem does not provide the present scalar/naturality statement. Smooth/Reduction.lean assumes coefficient compatibilities. Neither is an attachment.

## Wanted

None. The blueprint sources are present. These are explicitly agent-written integral auxiliary arguments, not claims that a Stacks tag states integral smooth trace compatibility. No forbidden source is used.

## Repairs and unfinished work

The released 2026-10-22 keep_plan order reopens this previously reviewed item. Three new statement-only nodes distribute its 7977-character proof; their proofs remain future stage-1 tasks. The item statement, all hypotheses, statement dependencies and Lean audit are unchanged. The old source.note mentioned a prohibited source despite the accepted proof using no such route; it is replaced with the actual diagonal/reconstruction route. The old Step 6 called the shifted object T_0 degree zero before stating its correct shifted interval: the new statement distinguishes the unit [0,0] from T_0 [-2d,-2d]. In the old Steps 12-13, u was sometimes written as though its source were P(HK). The new coefficient-calculus node explicitly inserts j and writes tilde-u for that composite, fixing the typing without changing a map.

## Not duplicates

lem-pur-adic-operation-domains-source-comparison vs lem-pur-integral-operations-scalar-extension: that node gives operation comparisons, not their uniform Tor domains, exact source functor, twisted source comparison with shifts and ordinary tensor normalization.
lem-pur-adic-operation-domains-source-comparison vs lem-pur-shifted-tate-unit-scalar-coherence: that node treats the shifted unit alone; the new node treats all K and the restricted adjunction domains.
lem-pur-adic-unit-trace-transpose-reductions vs thm-pur-adic-reconstruction: reconstruction is pointwise and asserts no compatible natural choice; the new node specifies a single unit trace and projection transpose for every coefficient field and input.
lem-pur-adic-unit-trace-transpose-reductions vs lem-pur-tower-trace-purity-comparison: that stronger comparison identifies a trace lift with an independent whole-tower family and depends on the present item; it cannot be cited without a cycle. The new node only proves finite reductions and invertibility of the specified trace transposes, without integral uniqueness.
lem-pur-adic-unit-trace-transpose-reductions vs lem-pur-tensor-trace-transpose: that is a finite-coefficient transpose identity, not construction and reduction of an integral trace over every finite field.
lem-pur-adic-trace-transpose-coefficient-calculus vs lem-pur-adic-scalar-trace-coherence: that node gives the scalar trace identity used as an explicit hypothesis here; the new node concerns its projection transposes and exceptional coefficient mates.
lem-pur-adic-trace-transpose-coefficient-calculus vs lem-pur-adic-projection-shift-coherence: that node gives shift compatibility for one trace and one coefficient field; the new node proves coherent coefficient mates and their scalar square and shifts.
lem-pur-adic-trace-transpose-coefficient-calculus vs lem-weil-pbc-mate-pasting: generic pasting alone does not compare integral projection-trace maps or their signed canonical shifts.
lem-pur-adic-trace-transpose-coefficient-calculus vs lem-pur-adic-purity-scalar-naturality: conditional calculus for arbitrary traces; it neither constructs normalized traces nor proves their transposes invertible. The item also needs the domain and trace-reduction arguments.

Blueprint search: ancestor returned thm-pur-rational-and-qbar-purity. Searches for adic purity, trace coefficient, mate shift, integral coefficient comparison, projection trace, scalar transpose, exact integral, reconstructed trace, trace transpose found no node stating a new argument. The one twist-definition hit and existing field-extension tower blueprint do not supply these three assertions independently. The item's existing same_as is retained. Whole-DAG keyword searches included the tower-trace comparison, generic tensor-arrow mate and integral realization shift nodes; their domains or conclusions differ as above.

## Review by Q124

I read the released repair note, the complete old proof and review, the master transport unit Steps 1-4 and current main-20261015 transport statement, and the actual sk-thm-sf-compatibility unit clause (7). The new nodes are agent auxiliary extractions of these sources, not replacements of finite smooth purity. Their report arguments below retain every former step verbatim. I read the statements of the old dependencies, especially the actual coefficient comparison's projection and shift clauses, the exceptional adjoint's finite-reduction counit comparison and Tor bounds, reconstruction's explicit absence of uniqueness, the finite universal trace, and the definitions of the tensor purity map and co-smoothness.

Assembly Step 1 cites the operation-domain node, whose statement gives each preserved domain, linearity and exactness needed before any Hom transpose, and the exact a and c comparisons. Step 2 cites the unit-trace node: its statement introduces the chosen g_0, every t_E, PF and j, then states naturality, prescribed finite reductions and invertibility. Step 3 cites the existing scalar-trace-coherence statement, with the same base coefficient field and the identical formula for t_E; it says precisely the trace equation required by Step 4. Step 4 cites the conditional coefficient-calculus node, whose hypotheses are satisfied by Steps 1-3. Its conclusion contains the explicitly typed definition of b, the scalar square, tensor associator equation, identities and shifts. The additional invertibility hypothesis on gamma is supplied by Step 2, so its final exactness and invertibility conclusion applies. Verbatim quotations for every assembly citation are in citations.json.

For the new operation node I checked that absolute dimension bounds, not relative d, are used for P and G; X or Y empty allows bound zero. Pullback and rank-one twist shift the common Tor interval as stated. Scalar extension is ordinary completed-ring tensor under chi; ramified quotient maps need no flatness, since the derived test uses n with en>=m. The shift on G is the one specified by the counit, not an arbitrary exact structure. For the new trace node the unit is [0,0] and its d-twist is [-2d,-2d]; reconstruction is used once at E_0. Finite trace comparison is first used at er, then further reduction to any m. Naturality is the projection/counit Hom-bijection calculation; finite purity gives zero reductions of the cone, and derived completeness detects its vanishing. No equality of arbitrary integral lifts is inferred.

For the coefficient-calculus node the traces are arbitrary subject to their displayed equation, and gamma is not assumed invertible until its conditional final conclusion. Each transpose has the source P_F C_X G_E K, using c inverse; tilde-u makes the projection-versus-H source identification explicit. The mate composition equation has the same X/Y associators as the item. The projection-shift statement permits T_E in degree -2d; its even sign is +1. Naturality of c and the counit identifies both scalar-square transposes. Identity fields, d=0, empty schemes, K=0, and nontrivial ramification cause no extra hypotheses. A zero trace is also permitted in the calculus: then gamma is zero and its final invertibility implication is simply not applicable.

I checked B-E against these files: unsplit nodes have statements only, with introduced objects and cited notions; no proofs or proof dependencies; no source tag is used as a definition; Mathlib searches are real logged commands and general adjunction/shift hits do not specialize in one line to these normalized geometric maps; no new node reproduces the whole item. I checked the cited statements rather than their proofs. The new statements do not cite the item, so they do not create a back edge. The report below retains old proof arguments for independent future workers, grouped into three comparable jobs.

## Retained arguments for the new statement-only nodes

### lem-pur-adic-operation-domains-source-comparison

Former Step 1: Choose nonnegative integers $D_X,D_Y$ bounding $\dim X,\dim Y$ by [lem-kun-dimension-finite-type], taking $0$ for an empty scheme. The compact-support bound of [lem-coef-integral-compact-support] sends a common interval $[a,b]$ to $[a,b+2D_X]$, while the exceptional-adjoint bound of [prop-coef-integral-exceptional-adjoint] sends it into $[a-2D_X,b+2D_Y]$. Thus $P_E=Rf_{!,E}$ and $G_E=Rf_E^!$ preserve the uniform finite-Tor domains, so the adjunction used below restricts to the stated full subcategories.

Cited statements: lem-coef-integral-compact-support, prop-coef-integral-exceptional-adjoint, lem-kun-dimension-finite-type. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Steps 2-3, checking the completed finite-Tor domains before coefficient passage.

Former Step 2: The pullback and completed tensor preserve derived-complete constructible objects by [lem-pur-integral-operations-preserve-constructible], and finite pullback preserves the Tor interval by [lem-sf-pullback-tor-amplitude]. The locally free rank-one twists of [lem-pur-twist-sheaf-locally-free] shift $[a,b]$ to $[a-2d,b-2d]$. The uniform domain is triangulated by [lem-weil-integral-ctf-triangulated].

Cited statements: lem-pur-integral-operations-preserve-constructible, lem-sf-pullback-tor-amplitude, lem-pur-twist-sheaf-locally-free, lem-weil-integral-ctf-triangulated. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Steps 2-3, checking the completed finite-Tor domains before coefficient passage.

Former Step 3: For $C_{F/E}$, exactness and associativity come from [lem-pur-derived-change-of-rings], comparison with strict scalar extension from [lem-weil-finite-free-completed-scalar-comparison], and constructible preservation from [lem-weil-integral-scalar-extension-constructible]. The same Tor interval survives each ramified extension by [lem-pur-adic-scalar-extension-tor-bound], without assuming quotient flatness.

Cited statements: lem-pur-derived-change-of-rings, lem-weil-finite-free-completed-scalar-comparison, lem-weil-integral-scalar-extension-constructible, lem-pur-adic-scalar-extension-tor-bound. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Step 3, scalar-extension domain and associativity checks.

Former Step 4: In the strict K-flat models of [lem-pur-integral-operations-well-defined], inverse image, tensor with a fixed twist, reduction, cone and shift are termwise compatible. The exact strict-tower derived-limit functor [lem-weil-pbc-ringed-strict-tower-homotopy-limit] therefore makes $H_E$ exact; termwise scalar multiplication makes it $\mathcal O_E$-linear.

Cited statements: lem-pur-integral-operations-well-defined, lem-weil-pbc-ringed-strict-tower-homotopy-limit. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Steps 2-3, exact strict limits and linearity.

Former Step 5: Construct $a_{F/E}$ from the pullback and tensor comparisons of [lem-pur-integral-operations-scalar-extension], the twists of [def-coefficient-twists-detailed], and the shift identification, transporting through $\chi$ of [lem-weil-finite-free-completed-scalar-comparison]. The compact-support comparison $c_{F/E}$ is [lem-pur-compact-support-integral-coefficient-comparison]. Balancing maps on K-flat representatives send $((x\otimes s)\otimes t)$ to $x\otimes st$ and $x\otimes1$ to $x$; [lem-pur-derived-change-of-rings] descends these identities and gives the unit, composition and shift laws for $a$.

Cited statements: lem-pur-integral-operations-scalar-extension, def-coefficient-twists-detailed, lem-weil-finite-free-completed-scalar-comparison, lem-pur-compact-support-integral-coefficient-comparison, lem-pur-derived-change-of-rings. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Step 3, scalar reassociations and compact-support coefficient comparisons.

### lem-pur-adic-unit-trace-transpose-reductions

Former Step 6: Put $E_0=\mathbf Q_\ell$, $\mathbf1_{0,W}=\widehat{\mathbf Z}_{\ell,W}$ and $T_0=\mathbf1_{0,X}(d)[2d]$. By [lem-weil-constant-coefficient-objects-constructible] it is constructible, derived complete and has reduction interval $[0,0]$. Apply [thm-pur-adic-reconstruction] once to choose $g_0:T_0\xrightarrow{\sim}G_0\mathbf1_{0,Y}$ with prescribed finite reductions, and define $t_0=\epsilon_{0,\mathbf1_0}\circ P_0(g_0)$. Its twist interval is $[-2d,-2d]$; [lem-coef-integral-compact-support] with absolute bound $D_X$ gives $P_0T_0$ and interval $[-2d,-2d+2D_X]$. Counit compatibility in [prop-coef-integral-exceptional-adjoint] identifies reductions of $t_0$ with [def-pur-smooth-trace].

Cited statements: lem-weil-constant-coefficient-objects-constructible, thm-pur-adic-reconstruction, lem-coef-integral-compact-support, prop-coef-integral-exceptional-adjoint, def-pur-smooth-trace, lem-kun-dimension-finite-type. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Step 2, choosing one reconstructed unit-coefficient morphism.

Former Step 7: For finite $E$ put $T_E=\mathbf1_{E,X}(d)[2d]$, $C_{E/0}=C_{E/\mathbf Q_\ell}$, and let $\theta_E:C_{E/0,X}T_0\xrightarrow{\sim}T_E$ be the Step 5 comparison (the twist and scalar-extension comparison $a$ at the unit, for $\mathbf Q_\ell\subset E$). Define $t_E=C_{E/0,Y}(t_0)c_{E/0,T_0}^{-1}P_E(\theta_E^{-1})$. For $K$ define $u_{E,K}$ as inverse projection followed by $t_E\widehat\otimes1$, using the order $T_E\widehat\otimes^LLf_E^*K$.

Cited statements: lem-pur-compact-support-integral-coefficient-comparison, fix-prop-projection-formula, prop-coef-integral-exceptional-adjoint. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Steps 2-3, scalar extension of the single integral trace.

Former Step 8: Take $\gamma_{E,K}$ to be the adjoint transpose of $u_{E,K}$, precomposed with the canonical identification $H_EK\cong T_E\widehat\otimes^LLf_E^*K$ (twist reassociation and tensor symmetry). For a morphism $v:K\to K'$, naturality of the projection map, tensor maps and counit gives $G_E(v)\gamma_{E,K}=\gamma_{E,K'}H_E(v)$ after applying the injective adjunction Hom bijection. The same Hom bijection is additive and $\mathcal O_E$-linear because $P_E,G_E,H_E$ and the counit are linear; hence the transpose is $\mathcal O_E$-linear in morphisms. This is the elementary adjoint-transpose calculation in the additive linear categories supplied by [prop-coef-integral-exceptional-adjoint], [lem-weil-compact-support-reduction-tower-functor] and [lem-weil-pbc-ringed-strict-tower-homotopy-limit].

Cited statements: prop-coef-integral-exceptional-adjoint, lem-weil-compact-support-reduction-tower-functor, lem-weil-pbc-ringed-strict-tower-homotopy-limit. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Steps 2-3, integral naturality and linearity.

Former Step 9: At cofinal $E$-levels $er$, [lem-pur-compact-support-integral-coefficient-comparison] reduces $t_E$ to the extension of $t_{A_r}$, which is the finite smooth trace by [lem-pur-finite-universal-smooth-trace]. Reducing $u_{E,K}$ with [fix-prop-projection-formula] gives the finite counit composite [def-pur-smooth-trace], and [prop-coef-integral-exceptional-adjoint] identifies its transpose with the reduction of $\gamma_{E,K}$. For arbitrary $m$, choose $er\ge m$ and use [thm-pur-finite-reduction-of-purity]. Thus reductions are the prescribed maps from [thm-pur-adic-reconstruction], invertible by [thm-pur-finite-coefficient-smooth-purity]. If $Q$ is the cone, [lem-weil-integral-ctf-triangulated] makes it derived complete; exact reduction [lem-pur-derived-change-of-rings] makes every reduction zero, and [def-weil-derived-complete] plus [lem-kun-distinguished-cone-zero] gives $Q=0$.

Cited statements: lem-pur-compact-support-integral-coefficient-comparison, lem-pur-finite-universal-smooth-trace, fix-prop-projection-formula, def-pur-smooth-trace, prop-coef-integral-exceptional-adjoint, thm-pur-finite-reduction-of-purity, thm-pur-adic-reconstruction, thm-pur-finite-coefficient-smooth-purity, lem-weil-integral-ctf-triangulated, lem-pur-derived-change-of-rings, def-weil-derived-complete, lem-kun-distinguished-cone-zero, def-pur-smooth-purity-map, def-pur-co-smoothness. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Steps 1-3, cofinal reductions and zero-cone detection.

### lem-pur-adic-trace-transpose-coefficient-calculus

Former Step 10: Define $b_{F/E,K}$ as the transpose of $C_Y(\epsilon_{E,K})c_{F/E,G_EK}^{-1}$ using [prop-coef-integral-exceptional-adjoint]. Naturality follows from naturality of $c$ and the counit.

Cited statements: prop-coef-integral-exceptional-adjoint, lem-pur-compact-support-integral-coefficient-comparison. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Step 3, exceptional coefficient comparison.

Former Step 11: The scalar-extended traces satisfy $t_F P_F(a_{F/E,\mathbf1_E})c_{F/E,T_E}=C_Y(t_E)$ by [lem-pur-adic-scalar-trace-coherence].

Cited statements: lem-pur-adic-scalar-trace-coherence. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Step 3, scalar trace transitivity.

Former Step 12: Tensor this trace identity with $C_YK$ and use the coefficient and projection compatibility of [fix-prop-projection-formula] to obtain $u_{F,C_YK}P_F(a_{F/E,K})c_{F/E,H_EK}=C_Y(u_{E,K})$.

Cited statements: fix-prop-projection-formula. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Step 3, projection compatibility of trace-valued maps.

Former Step 13: Transpose the two sides under $P_F\dashv G_F$. Naturality of $c^{-1}$ and the definition of $b$ make the transpose of $b_KC_X(\gamma_{E,K})$ equal to $C_Y(u_{E,K})c_{H_EK}^{-1}$, while the transpose of $\gamma_{F,C_YK}a_K$ is $u_{F,C_YK}P_F(a_K)$. The preceding identity and injectivity of the adjunction Hom bijection prove the purity square. Since $a$ and both purity maps are isomorphisms, $b$ is an isomorphism.

Cited statements: prop-coef-integral-exceptional-adjoint, lem-pur-compact-support-integral-coefficient-comparison, fix-prop-projection-formula. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Step 3, scalar purity square.

Former Step 14: The tensor formula of Step 5 gives the associator and identity equations for $a$. Apply [lem-weil-pbc-mate-pasting] to the three adjunctions and inverse coefficient squares $c_{F/E}^{-1},c_{L/F}^{-1}$. The mate of the pasted square is $b_{L/F,C_{F/E,Y}K}C_{L/F,X}(b_{F/E,K})$, and the composition equation for $c$ in [lem-pur-compact-support-integral-coefficient-comparison] identifies the paste with $c_{L/E}^{-1}$. This is the displayed equation for $b$; the identity extension gives $b_{E/E}=1$.

Cited statements: lem-weil-pbc-mate-pasting, lem-pur-compact-support-integral-coefficient-comparison. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Step 3, three-field coherence.

Former Step 15: The compact-support functor is exact and has its specified shifts by [lem-weil-compact-support-reduction-tower-functor] and [lem-weil-pbc-ringed-strict-tower-homotopy-limit]. The canonical adjunction shift comparison for $G_E$ is characterized by the counit through $\operatorname{Hom}(M,G_E(K[1]))\cong\operatorname{Hom}(P_EM,K[1])\cong\operatorname{Hom}(P_E(M[-1]),K)\cong\operatorname{Hom}(M[-1],G_EK)$.

Cited statements: lem-weil-compact-support-reduction-tower-functor, lem-weil-pbc-ringed-strict-tower-homotopy-limit, prop-coef-integral-exceptional-adjoint. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Step 3, canonical shift comparisons.

Former Step 16: The compact-support projection map commutes with shifting its second input, including proper and open constituents, by [lem-pur-adic-projection-shift-coherence]. Its proof uses [def-exchange-projection], the proper mate shift [lem-weil-pbc-ringed-projection-mate-exact], and exact extension by zero and its projection formula [lem-cbc-proetale-extension-zero, lem-cbc-extension-zero-projection-formula].

Cited statements: lem-pur-adic-projection-shift-coherence, def-exchange-projection, lem-weil-pbc-ringed-projection-mate-exact, lem-cbc-proetale-extension-zero, lem-cbc-extension-zero-projection-formula. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Step 3, projection-formula shift calculation.

Former Step 17: Consequently $u_{E,K[1]}=u_{E,K}[1]$ and $\gamma_{E,K[1]}=\gamma_{E,K}[1]$ by [lem-pur-adic-projection-shift-coherence] applied with $T=T_E$ and $t=t_E$; the identification $H_EK\cong T_E\widehat\otimes^LLf_E^*K$ of Step 8 commutes with the shift in $K$, the Koszul sign of moving the shift past $T_E$ (in degree $-2d$) being $(-1)^{2d}=1$. Exactness of $H_E$ and the shifted adjunction make $G_E$ exact on the finite-Tor categories. Since $c$ commutes with shift by [lem-pur-compact-support-integral-coefficient-comparison], transposing its shifted defining composite gives $b_{F/E,K[1]}=b_{F/E,K}[1]$. Applying this to the purity square proves its shift compatibility.

Cited statements: lem-pur-adic-projection-shift-coherence, lem-pur-compact-support-integral-coefficient-comparison, prop-coef-integral-exceptional-adjoint. Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-thm-purity-transport/_section.md, Unit Step 3, shift compatibility of purity and coefficient comparisons.

The arguments above are the source material of the unsplit nodes, not proof steps embedded in their statements. Former Steps 11 and 16 retain their existing lemma references; they are not duplicated as additional nodes. No Lean file, compiler, Lake command or repository write was used.

## Validation

First dry run rejected the final citation excerpt as too short. All four excerpts now contain their cited statements verbatim, so they expose every clause used by the assembly.
