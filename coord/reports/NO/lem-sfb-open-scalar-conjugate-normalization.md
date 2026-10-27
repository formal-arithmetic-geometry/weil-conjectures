# Stage-1 repair: lem-sfb-open-scalar-conjugate-normalization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-open-scalar-conjugate-normalization.json`: unchanged statement; five assembly steps, 2875 characters in total.
- `dag/nodes/sec-six-functors-basics/lem-sfb-open-coefficient-square-action-identification.json`: statement, unsplit; no Mathlib match. Carries the ordinary action and specified coefficient-square normalization, including localization (old steps 2–3).
- `dag/nodes/sec-six-functors-basics/lem-sfb-open-internal-kflat-mate-normalization.json`: statement, unsplit; no Mathlib match. Carries the comparison of the sectionwise K-flat normalization with the actual internal scalar adjunctions and its transpose equation (old step 5).
- `citations.json`: exact statement quotations for every use in the five parent steps.

## Attachments

None. `AlgebraicGeometry.ProEtale.CondensedRing.open_scalar_conjugate_normalization` in `lean/Sheaf/SixFunctors/OpenScalarConjugateNormalization.lean:69` has `sorry` at the end of its proof. No declaration under `lean/WeilConjectures/` found by the item tag or scalar/conjugate concept states this normalization. The underived and derived comparison definitions in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean:177,191` specify the maps but do not state the new component or transported-mate identities.

## WANTED

None.

## What was wrong and what was repaired

The return requires spreading the 7497-character proof across independently claimable nodes. There was no retained node, report, citation file or search log in this sandbox: only dispatcher marker files. I copied the current reviewed item from the shared repository, which contains the returned seven-step proof and its reviewer correction to step 5. The initial required dry run exited because report.md did not yet exist. I retained all existing statement, source, blueprint, Lean and review metadata. No target, chapter or unit statement changed.

The two new statement-only nodes are independent of each other and of the parent: neither depends on the parent or on the other new node. The first carries 2756 characters of the original argument (steps 2–3); the second carries 1633 characters (step 5), including the nontrivial internal-to-sectionwise transfer that the previous reviewer inserted. Both have `proof: []`, `proof_deps: []`, `proof_origin: null`, and status `unsplit`. The parent retains the full successive-Hom, composite-unit and four-line transpose calculation, then cancels the actual invertible units. It is now 2875 characters. No clause of the parent's final formula is made into a replacement lemma. This is the requested exception to keeping short elementary calculations inline: the action-square comparison and derived transport are extracted as separate arguments for parallel work, rather than erased or relabelled.

## Argument allocation

| Original steps | Location after repair | Work retained |
|---|---|---|
| 1 | Parent step 1, used in step 2 | Actual four adjunctions, directions, successive Hom bijections and their units. |
| 2–3 | lem-sfb-open-coefficient-square-action-identification | Balanced collapse and inverse; common coefficient action and naturality; the specified comparison, not an arbitrary isomorphism; degreewise differential compatibility and localization. |
| 4 | Parent step 2 | Both composite-unit transposes and equation (1), with the specified conjugate. |
| 5 | lem-sfb-open-internal-kflat-mate-normalization, applied in parent step 3 together with lem-sfb-open-coefficient-square-action-identification | The fixed internal/sectionwise equivalences, scalar units, pullbacks and balanced generators; K-flat normalization on all unbounded objects; scalar inverse-mate transpose and equation (2). |
| 6 | Parent step 4 | Naturality of scalar unit, equation (2), naturality of the square, equation (1), cancellation and injectivity of Hom adjunction. |
| 7 | Parent step 5 | Cancel the actual invertible open units and theta, retain naturality and absence of flatness or boundedness. |

The complete original arguments are reproduced verbatim below as handoff material. They are deliberately outside the new nodes' statements: future workers receive propositions, not unsplit statements containing proof sketches.

## Searches and source reading

The item searches in the reviewed node are unchanged and retained. For each new node I ran leanfinder, Loogle, grep and LeanSearch through the authorized msearch.py command, with a second semantic phrasing before concluding no match. `searches.jsonl` contains the actual queries and responses' digests; the nodes record exactly those query texts and their observed hit names. All services answered. One preliminary Loogle query used an unknown internal-module identifier; I retained that result and then used the valid `SheafOfModules.restrictScalars, SheafOfModules.pullback` query. It returned zero hits. I read the candidate generic unit-mate formula at Mathlib/CategoryTheory/Adjunction/Mates.lean:136 and the ordinary pullback-composition conjugacy at Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:177. They do not supply the identification of the sectionwise K-flat comparison with the specified internal operations. The structure-sheaf open restriction isomorphism at Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:453 is about a different coefficient category and does not normalize the published condensed restriction square. No search was invented or unavailable result labelled absent.

I read the chapter and unit records, current main-20261015 `det-prop-scalar-six-pullback.proof.md` (1) and (2), `def-sfb-comap-upper-star-iso.proof.md`, `def-sfb-derived-comap-upper-star-iso.md` and `def-sfb-derived-open-immersion-shriek-iso.md`. The first new node's source is the explicit transport and invertible coefficient-square composite in the comparison proof, with the reviewed parent's steps 2–3 giving the component calculation to hand off. The second's source is the balanced K-flat argument in (1), applied to the internal module categories as in the reviewed parent's step 5. The new statements mark these as extracted arguments. They use the existing K-flat, section-scalar and internal-operations nodes for the general input, rather than claiming that the blueprint already contains all of the transfer calculation. For the parent's formal conjugacy I read Stacks categories.tex Tag 0B65, label lemma-transformation-between-functors-and-adjoints, and Tag 0DV0, label lemma-compose-counits. The unit version is explicit in def-weil-pbc-composite-adjunction. No SGA route is used.

Whole-DAG and blueprint searches included `comap upper star`, `comapUpperStarIso`, `extend-comap`, `restriction of scalars`, `K-flat`, `scalar mate`, `scalar-comparison-normalization`, `internal-section-scalar`, `action identification` and `balanced`; direct DAG searches included coefficient-square, action identification, collapse, scalar transpose and transported mate. I opened the relevant comparison, transport and normalization statements rather than treating the search output as evidence of their content. Both blueprint references have ancestor det-prop-scalar-six-pullback, a precise place, via [lem-sfb-open-scalar-conjugate-normalization], and same_as []. Their generic inputs are existing nodes; neither new statement already appears as a blueprint proposition.

## Not duplicates

lem-sfb-open-coefficient-square-action-identification vs def-sfb-comap-upper-star-iso: the existing statement gives a natural isomorphism, but does not assert that its specified components are the identity after balanced coefficient collapses or identify its localized inverse with the action square.
lem-sfb-open-coefficient-square-action-identification vs def-sfb-derived-comap-upper-star-iso: the existing statement gives the levelwise derived isomorphism; the new statement determines that specified isomorphism under the action identifications, including its inverse.
lem-sfb-open-coefficient-square-action-identification vs def-sfb-extend-comap-iso-of-iso: this general coefficient-square isomorphism supplies one constituent; it does not identify the full published open comparison after transport and localization.
lem-sfb-open-coefficient-square-action-identification vs def-sfb-comap-mapmod-square: that statement is a restriction/transport square, while the new node also includes the two extensions along alpha and their prescribed balanced collapses in the actual open pullback.
lem-sfb-open-internal-kflat-mate-normalization vs lem-sfb-kflat-scalar-comparison-normalization: the latter is for sectionwise module sheaves and does not state the identification with the actual internal module-object derived scalar adjunctions.
lem-sfb-open-internal-kflat-mate-normalization vs lem-sfb-internal-section-scalar-adjunction: the latter handles scalar operations at a single site; it does not identify the geometric pullback mate or balanced K-flat pullback square across two sites.
lem-sfb-open-internal-kflat-mate-normalization vs lem-sfb-internal-module-operations-transport: the latter identifies ordinary geometric operations and adjunctions, not the derived scalar/pullback comparison and its scalar transpose.
lem-sfb-open-internal-kflat-mate-normalization vs lem-sfb-derived-section-scalar-transport: the latter transports a scalar adjunction conditional on ordinary squares. It does not assert the normalization of the geometric balanced K-flat tensor comparison across the open inverse image.
lem-sfb-open-internal-kflat-mate-normalization vs lem-sfb-scalar-adjunction-unit-coefficient-normalization: that node concerns the constant residue quotient Z to Z/n, a single scalar unit and shifts, without the geometric inverse-image square or arbitrary condensed coefficients.
lem-sfb-open-internal-kflat-mate-normalization vs lem-sfb-open-coefficient-square-action-identification: the first identifies the normalized derived scalar mate under internal/sectionwise equivalences, while the second determines the separately specified right-adjoint square. They share inputs but prove distinct comparisons.

Neither new source claims an additional Stacks-tag theorem; the underlying Stacks facts are cited by the existing normalization/transport nodes and are not recreated as tag-sharing leaves.

## Review by NO

I checked the full B–E checklist against the actual statements and sources. Both new propositions introduce a, j, all coefficient rings and maps, functors and comparison maps themselves, cite their definition nodes, use single-escaped TeX in JSON, and carry no proof steps. The second defines theta as the transported balanced comparison, so the assertion that it is the mate of d is substantive, not a tautological redefinition of theta. The first determines the actual c and its inverse rather than just asserting existence. They are substantially smaller arguments, not clauses of the final open-unit cancellation formula. The seven old arguments are all allocated above and preserved below.

In parent step 1, coefficient-change supplies T adjoint to r, derived-comap supplies the square c, derived-open-shriek and conjugate-pull identify exactly beta as its conjugate, and composite-adjunction states both the actual composite units and successive Hom bijections. In step 2 these same conjugate and composite statements give equation (1) by transposing beta and the identity. I checked the directions: beta maps T_X J_A M to J_B T_U M; c maps r_U R_B to R_A r_X, so c_N postcomposes the transpose of the latter identity. No generic fully-faithful or unrelated Yoneda statement is substituted.

In step 3 the first new statement gives exactly c inverse equals d, and the second gives the displayed scalar-unit transpose equation for d, plus invertibility of theta under the actual scalar adjunctions. Both have the same coefficients, unbounded derived categories, inverse coefficient identifications and open j as the item. The pre-existing K-flat lemma is explicitly sectionwise; the extracted second statement retains the necessary internal-to-sectionwise transfer and units, which would be missing in a direct application. The internal scalar node states its comparisons preserve balanced generators, units and counits on unbounded categories; the operations node states the corresponding pullback comparison. These are the claims the extracted transfer uses.

In step 4 only the already obtained equations (1) and (2), scalar adjunction, and naturality are used: I checked each of the four lines and the objects V=J_A M and N=J_B T_U M. The third line is naturality at beta_M, and the fourth cancels c_N inverse c_N. The coefficient-change statement supplies the exact Hom adjunction needed for injectivity. Step 5 is elementary cancellation of invertible transformations already given in the item and step 3. Natural identities remain natural after cancellation. citations.json quotes exactly the relevant statements for all uses in steps 1–4; step 5 cites none.

For edge cases I checked j=id (the collapse and action maps reduce to identity and the formula reduces to cancellation), U empty (all module maps on the open are uniquely determined), M=0, and a non-flat coefficient change such as the discrete condensed Z to Z/2. The collapse only needs alpha invertible, not a flat; the derived normalization uses K-flat representatives rather than assuming scalar extension exact. I also checked the coefficient equation alpha_B F(a_X)=a_U alpha_A is in the coefficient-change statement, the common action runs from A_U to F(B_X), and each inverse-mate transpose is correctly typed. No boundedness assumption or standing-scheme finiteness was added. No statement dispute arose.

The existing off-unit tool-use declarations for alpha-iso and internal-module-operations-transport are retained in the parent metadata; the new nodes are unsplit and declare the corresponding statement dependencies. No other route is introduced. Neither statement depends on the parent, so the extraction creates no circularity. The parent has no proof step over 2000 characters. Server check_dag and review_split were run through srvcheck and passed before the final delivery dry run; the full delivery preflight is the final gate.

## Unfinished work

Exactly the two new statement-only arguments are left for later workers, as required by the repair. This is a stage-1 delivery; no Lean was written or compiled, no repository or launcher file was modified, no agents were started, and no git command was run in the read-only repository.

## Preserved original argument and worker handoff

### Original step 1

Write $J_A=j_{!,A}$, $J_B=j_{!,B}$, $R_A=j_A^*$, $R_B=j_B^*$, and $r_T=D(\operatorname{Res}_{a_T})$. The scalar adjunctions $T_T\dashv r_T$ are supplied by [sk-def-sfb-coefficient-change]; denote their units by $\eta_T$. Denote the specified restriction square of [def-sfb-derived-comap-upper-star-iso] by
$$c:r_UR_B\xrightarrow{\sim}R_Ar_X.$$
By [def-sfb-derived-open-immersion-shriek-iso] the specified $\beta:T_XJ_A\xrightarrow{\sim}J_BT_U$ is its conjugate. In the convention of [def-sfb-conjugate-pull-iso], $\beta$ corresponds to $c$, with the adjunctions $J_BT_U\dashv r_UR_B$ and $T_XJ_A\dashv R_Ar_X$. Their Hom bijections are the successive individual Hom bijections, by [def-weil-pbc-composite-adjunction]. Keep these adjunctions and the actual open units $u_A,u_B$ of the statement throughout.

Uses: sk-def-sfb-coefficient-change, def-sfb-derived-comap-upper-star-iso, def-sfb-derived-open-immersion-shriek-iso, def-sfb-conjugate-pull-iso, def-weil-pbc-composite-adjunction.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-coefficient-comparisons/def-sfb-derived-open-immersion-shriek-iso.md; Definition: conjugate along the two composite adjunctions.

### Original step 2

We first check which action square $c$ represents. Put $F=j^{-1}$ on abelian sheaves, $\alpha_A=\alpha_j^\Lambda$, and $\alpha_B=\alpha_j^{\Lambda\prime}$. In this paragraph let $N$ be an ordinary $B_X$-module and use $R,r$ also for the ordinary pullback and scalar-restriction functors. In the pullback formula of [sk-def-sfb-module-pushforward-pullback], identify $\operatorname{Ext}_{\alpha_A}FN$ with $FN$ having action restricted along $\alpha_A^{-1}$, and likewise for $B$; these identifications are available because [lem-sfb-alpha-iso] makes both coefficient maps invertible. Using the coequalizer definition of extension in [sk-def-sfb-change-of-scalars], the identifications have balanced-tensor formulas $x\otimes n\mapsto\alpha_A^{-1}(x)n$ and $n\mapsto1\otimes n$. The action makes the first map balanced; its composite with the second is the identity, and the other composite is $x\otimes n\mapsto1\otimes\alpha_A^{-1}(x)n=x\otimes n$ by the balancing relation. By [sk-def-sfb-coefficient-change], $\alpha_B F(a_X)=a_U\alpha_A$, hence $\alpha_B^{-1}a_U=F(a_X)\alpha_A^{-1}$. Thus the actions on $r_U R_BN$ and $R_A r_XN$ coincide on the same object $FN$: both are restriction of the $F(B_X)$-action along this common composite. Here transporting an action and restricting it commute directly: for the monoidal structure $\mu$ of $F$, naturality gives $F(\gamma_N(a_X\otimes1))\mu=F\gamma_N\mu(F(a_X)\otimes1)$, using [sk-def-sfb-transport] and the restriction formula in [sk-def-sfb-change-of-scalars]. Both routes send a morphism $h$ to $Fh$.

Uses: sk-def-sfb-module-pushforward-pullback, lem-sfb-alpha-iso, sk-def-sfb-change-of-scalars, sk-def-sfb-coefficient-change, sk-def-sfb-transport.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-coefficient-comparisons/def-sfb-comap-upper-star-iso.proof.md; Transport/restriction action calculation and coefficient-square calculation, written out.

### Original step 3

The ordinary comparison [def-sfb-comap-upper-star-iso] is the composite of the transport/restriction comparison with the invertible coefficient-square comparison [def-sfb-extend-comap-iso-of-iso]. Unfold these specified comparisons using step 2: the transport comparison is the identity on $FN$, and the coefficient-square comparison, between the two tensor presentations, is the inverse collapse for $A$ after the collapse for $B$. On inverse-image modules its formula is consequently $n\mapsto n$; its inverse has the same formula. In particular this is precisely the action identification, with no automorphism of $FN$ inserted. The square [def-sfb-derived-comap-upper-star-iso] is the levelwise version of this comparison. In every degree the above formulas and their inverses commute with the differential, since they commute with every module morphism. Applying the localization functor preserves these equalities and inverse identities. Therefore on the derived categories, after the coefficient identifications used in the statement, $c^{-1}:R_Ar_X\to r_UR_B$ is exactly the action identification whose scalar-adjunction mate is $\theta_j$ in [lem-sfb-kflat-scalar-comparison-normalization].

Uses: def-sfb-comap-upper-star-iso, def-sfb-extend-comap-iso-of-iso, def-sfb-derived-comap-upper-star-iso, lem-sfb-kflat-scalar-comparison-normalization.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-coefficient-comparisons/def-sfb-comap-upper-star-iso.proof.md; Final displayed composite; derived levelwise construction in def-sfb-derived-comap-upper-star-iso.md.

### Original step 4

For $M\in D(U,A_U)$ put $V=J_AM$ and $N=J_BT_UM$. Transpose $\beta_M:T_XV\to N$ under the composite $T_XJ_A\dashv R_Ar_X$. The result is $R_Ar_X(\beta_M)\circ R_A(\eta_{X,V})\circ u_{A,M}$, by the composite-unit formula of [def-weil-pbc-composite-adjunction]. On the other hand, $1_N$ transposes under $J_BT_U\dashv r_UR_B$ to $r_U(u_{B,T_UM})\circ\eta_{U,M}$. By the defining Hom correspondence of [def-sfb-conjugate-pull-iso], postcomposition of this second transpose by $c_N$ is the first transpose: precomposition of $1_N$ by the specified conjugate $\beta_M$ is $\beta_M$. Consequently
$$R_Ar_X(\beta_M)\circ R_A(\eta_{X,V})\circ u_{A,M}
=c_N\circ r_U(u_{B,T_UM})\circ\eta_{U,M}.\tag{1}$$
This uses the actual conjugate specified in [def-sfb-derived-open-immersion-shriek-iso], rather than choosing another isomorphism between the same left adjoints.

Uses: def-weil-pbc-composite-adjunction, def-sfb-conjugate-pull-iso, def-sfb-derived-open-immersion-shriek-iso.
Source: literature/stacks-project/categories.tex; Tag 0B65, lemma-transformation-between-functors-and-adjoints: defining Hom correspondence; composite units expanded as in Tag 0DV0, lemma-compose-counits.

### Original step 5

The K-flat lemma concerns sectionwise module sheaves; transport it along the underlying-sheaf-preserving equivalences $E_T$ with module objects. They identify $T_T$, $r_T$ and the specified derived scalar adjunctions (unit $m\mapsto1\otimes m$) by [lem-sfb-internal-section-scalar-adjunction], and $R_A,R_B$ with the sectionwise pullbacks along $j^{-1}\Lambda_{X,\mathrm{sec}}\cong\Lambda_{U,\mathrm{sec}}$ induced by $\alpha$ by [lem-sfb-internal-module-operations-transport]. These comparisons send generators to generators, so after the collapses of step 2 they are the identity on $FN$: $c^{-1}$ corresponds to the lemma's identification $h_A^*r_Y=r_Xh_B^*$ for $h=j^{-1}$, rings identified by [lem-sfb-alpha-iso], and the mate is taken under the adjunctions $T\dashv r$ of steps 1 and 6. By [lem-sfb-kflat-scalar-comparison-normalization] and step 3, the specified $\theta_V:T_UR_AV\to R_BT_XV$ is the scalar-adjunction mate of $c^{-1}$. Its transpose under $T_U\dashv r_U$ is therefore
$$r_U(\theta_V)\circ\eta_{U,R_AV}
=c^{-1}_{T_XV}\circ R_A(\eta_{X,V}).\tag{2}$$
Indeed, the inverse-mates formula of [def-weil-pbc-adjunction-mate] inserts the scalar unit on the $X$ side, applies $c^{-1}$, and then contracts the $U$-scalar counit; transposing contracts that counit with its unit and leaves exactly the displayed right side. The K-flat normalization lemma identifies this mate with the balanced tensor comparison on the entire ordinary unbounded derived category and says it is invertible without flatness of $a$. Thus (2) is available at the possibly unbounded object $V=J_AM$, and $\theta_V^{-1}$ is the specified inverse.

Uses: lem-sfb-kflat-scalar-comparison-normalization, def-weil-pbc-adjunction-mate, lem-sfb-internal-section-scalar-adjunction, lem-sfb-internal-module-operations-transport, lem-sfb-alpha-iso.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-pullback.proof.md; (1) balanced K-flat comparison, applied to j; scalar mate expanded by its unit/counit formula.

### Original step 6

Set $d=R_B(\beta_M)\circ\theta_V\circ T_U(u_{A,M}):T_UM\to R_BJ_BT_UM$. Under $T_U\dashv r_U$ from [sk-def-sfb-coefficient-change], its transpose is $r_U(d)\circ\eta_{U,M}$. Naturality of $\eta_U$ at $u_{A,M}$, then (2), gives
$$\begin{aligned}
r_U(d)\eta_{U,M}
&=r_UR_B(\beta_M)\,r_U(\theta_V)\eta_{U,R_AV}\,u_{A,M}\\
&=r_UR_B(\beta_M)\,c^{-1}_{T_XV}\,R_A(\eta_{X,V})\,u_{A,M}\\
&=c_N^{-1}\,R_Ar_X(\beta_M)\,R_A(\eta_{X,V})\,u_{A,M}\\
&=r_U(u_{B,T_UM})\eta_{U,M}.
\end{aligned}$$
The third line is naturality of $c^{-1}$ at $\beta_M:T_XV\to N$; the last line substitutes (1) and cancels $c_N^{-1}c_N$. The final expression is exactly the transpose of $u_{B,T_UM}$. Injectivity of the adjunction Hom bijection yields
$$R_B(\beta_M)\circ\theta_V\circ T_U(u_{A,M})=u_{B,T_UM}.\tag{3}$$

Uses: sk-def-sfb-coefficient-change.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-pullback.proof.md; (2), alternative common-right-adjoint argument: explicit equality of scalar transposes.

### Original step 7

The units $u_A,u_B$ are the invertible open units specified in the statement, and $\theta$ is invertible by step 5. Postcompose (3) by $u_{B,T_UM}^{-1}$, then precompose by $T_U(u_{A,M}^{-1})\circ\theta_V^{-1}$. Functoriality gives $T_U(u_{A,M})T_U(u_{A,M}^{-1})=1$, so
$$u_{B,T_UM}^{-1}\circ R_B(\beta_M)=T_U(u_{A,M}^{-1})\circ\theta_V^{-1},\qquad V=J_AM,$$
which is the required formula. Every transformation used above is natural and all equations hold for arbitrary $M$, so this is a natural identity. Only the invertibility already specified for the open units and the unbounded K-flat normalization are used; no flatness or boundedness hypothesis has entered.

Uses: .
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-pullback.proof.md; (2), alternative open-adjunction argument: cancel the specified invertible units and normalized comparison.
