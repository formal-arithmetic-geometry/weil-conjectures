## Worker report

Repair by Q95, 2026-10-22, of the returned long split of lem-pur-diagonal-section-pasting. This is stage 1 only. The item statement is unchanged verbatim, and no Lean was written or compiled. The dispatched sandbox contained only dispatcher marker files, so I copied the current read-only repository node and used its retained twelve-step proof as the repair baseline. There was no earlier sandbox split, report or search log to supersede. The delivery tool rebases this packet onto current server main while preserving maintainer fields.

### Files written

- dag/nodes/sec-smooth-purity/lem-pur-diagonal-section-pasting.json: statement unchanged; three assembly steps, 1998 characters total.
- dag/nodes/sec-smooth-purity/lem-pur-affine-difference-tower-factorization.json: statement; unsplit; no Mathlib match. Factorization of affine difference charts through a Cartesian tower.
- dag/nodes/sec-smooth-purity/lem-pur-difference-coordinate-section-identifications.json: statement; unsplit; no Mathlib match. Identification of the diagonal-section inputs with the actual difference charts.
- dag/nodes/sec-smooth-purity/lem-pur-double-diagonal-section-identifications.json: statement; unsplit; no Mathlib match. Canonical restrictions through the two Cartesian diagonal squares.
- dag/nodes/sec-smooth-purity/lem-pur-dualizing-sigma-cocycle-locality.json: statement; unsplit; no Mathlib match. Dualizing tensor cocycle and normalized etale source locality.
- dag/nodes/sec-smooth-purity/lem-pur-etale-cartesian-tower-tensor-comparison.json: statement; unsplit; no Mathlib match. Dualizing tensor comparison through a Cartesian square and etale factors.
- dag/nodes/sec-smooth-purity/lem-pur-smooth-exceptional-tensor-pasting.json: statement; unsplit; no Mathlib match. Smooth exceptional base-change mates and tensor-composition pasting.
- report.md and citations.json: substantive self-review, verbatim citation witnesses and the complete retained argument below.
- searches.jsonl and search-*.txt: genuine msearch results retained with full hits; these are supporting sandbox material.

### Attachments

None. Searches in lean/WeilConjectures for the item tag, section-pasting names and diagonal-pasting terms found no declaration stating this item. The similarly named torsor diagonal sections are about another notion. lean/Sheaf/Paper/PurityDiagonalSectionPasting.lean ends in theorem WeilConjectures.PurityFiniteSetting.DiagonalPasting.diagonalSectionPasting with proof sorry, and therefore does not establish an attachment. The old Lean module and its twelve proof obligations were read only as retained mathematical material.

### WANTED

None. All sources used are available locally. No SGA source is used.

### What was wrong and what changed

The returned proof assigned 12555 characters of work to one item. Six substantial arguments are now six independently schedulable statements, all with empty proof, empty proof_deps, null proof_origin, and status unsplit. No new statement restates the whole item. The parent retains the cancellation that proves its global equation and the substitution that proves its coordinate equation. Open restriction is assembled by applying a generic locality theorem for the canonical operations to those particular expressions.

The old proof is not discarded or abbreviated: all twelve steps, including their original uses, are copied verbatim below. The distribution is:

| Old steps | New owner | Argument still required of the owner |
| --- | --- | --- |
| 2-3 | lem-pur-smooth-exceptional-tensor-pasting | horizontal and vertical exchange mates, tensor base change, compatible derived reassociation |
| 1, 4 | lem-pur-double-diagonal-section-identifications | actual Cartesian squares, permanence, gamma and the three canonical alpha identities |
| 6-7 | lem-pur-dualizing-sigma-cocycle-locality | specified sigma cocycle, normalized source-etale restriction and compatibility with beta; expression locality |
| 8-9 | lem-pur-affine-difference-tower-factorization | standard affine tower, genuine Cartesian R, translated etale difference maps and section equations |
| 10 | lem-pur-etale-cartesian-tower-tensor-comparison | the three typed tower identities (a), (b), (c), including composite E normalization |
| 11; output part of 12 | lem-pur-difference-coordinate-section-identifications | identify actual first and second chart inputs and actual composite output with normalized E and beta |
| 5; final substitution of 12 | parent assembly steps 1 and 3 | pull the two tensor identities to the section and substitute the canonical identifications |

The coordinate statement is conditional on charts, so existence of charts is not a hypothesis needed in the assembly. Nevertheless the geometry node also states their local availability at every point, preserving the argument of old step 12 as an explicit future obligation; applying sbc-thm-etale-local-normal-form first to g and then to f gives precisely these neighbourhoods. Empty and zero-dimensional cases remain included. In writing the self-contained coordinate-input node I corrected tau_g to be the forward beta from pullback of the V-model to the U-model; only delta_d is the inverse beta. I also made every base-change arrow in the generic statements separated finite type, as required by the exact exchange-pasting node used in their retained arguments. This adds no assumption to the parent: its projections, sections, diagonals and affine-chart arrows have those properties.

### What remains

The six new statements deliberately remain unsplit for other workers, as required by this return. Their complete inherited arguments are preserved below. No mathematical obligation from the old packet is represented by True, an unspecified comparison, or a per-cohomology replacement for a derived-object isomorphism.

## Not duplicates

Searches covered every dag/nodes chapter and the entire imported blueprint via tools/blueprint_refs.py, including diagonal section, exceptional base change, tensor composition, difference coordinates, dualizing composition, diagonal base change, etale normalization, Cartesian etale and tensor formula. I additionally searched statement text for sigma, difference-coordinate, exceptional pasting, Cartesian tensor towers and diagonal restriction. Reading the nearby candidates showed:

- lem-pur-smooth-exceptional-tensor-pasting vs fix-lem-exchanges: the existing theorem states direct-image exchange pasting; the new theorem identifies the exceptional counit mates and their tensor-transpose compatibility, with explicit coefficient domains.
- lem-pur-smooth-exceptional-tensor-pasting vs thm-pur-cohomological-smoothness: the existing tensor/base-change compatibility is an input, but does not state the vertical exceptional-pasting equation or its explicit sigma specialization.
- lem-pur-double-diagonal-section-identifications vs lem-pur-diagonal-base-change: the existing theorem identifies a single diagonal invariant; the new one gives the double-diagonal Cartesian geometry and identities relating its three alpha maps to gamma and A,B,D.
- lem-pur-dualizing-sigma-cocycle-locality vs lem-pur-finite-etale-dualizing-normalization: the existing theorem normalizes individual E and beta maps; the new theorem is the smooth triple tensor cocycle, its mixed etale consequence and their source-restriction pasting.
- lem-pur-dualizing-sigma-cocycle-locality vs lem-pur-dualizing-unit-composite: the existing theorem evaluates theta at the tensor unit and sigma when a factor is trivial; it does not prove the triple-sigma cocycle or mixed beta restriction.
- lem-pur-dualizing-sigma-cocycle-locality vs lem-pur-system-tensor-transpose-composition: the existing theorem concerns full normalized strict coefficient systems with specified system models and projection maps; specializing its conclusion requires a finite-level realization comparison, not a one-line instance of the new finite geometric statement. The present finite route already follows cohomological smoothness composition and adjunction conjugation.
- lem-pur-dualizing-sigma-cocycle-locality vs lem-asd-exceptional-base-change-open-restriction: the existing assertion propagates invertibility under target opens, in unbounded etale categories; it does not identify the normalized source-etale tensor maps.
- lem-pur-affine-difference-tower-factorization vs sbc-thm-etale-local-normal-form: that theorem provides one local chart; the new result factors two fixed centred charts through R and gives all Cartesian and zero-section equations. No new chart-existence assertion is created.
- lem-pur-etale-cartesian-tower-tensor-comparison vs lem-pur-finite-etale-dualizing-normalization: the existing clause (3) gives equation (a), but not the triple-tensor reassociation (b) or the second etale factor (c). These are a separate finite-tower argument, not an additional normalization lemma.
- lem-pur-difference-coordinate-section-identifications vs lem-pur-diagonal-dnc-chart-normalization: the latter identifies an oriented DNC/normal-bundle assembly and a single chart; the new statement identifies two simultaneous, orientation-free tensor inputs and the composite chart output, with their actual beta routes.
- lem-pur-difference-coordinate-section-identifications vs def-pur-affine-diagonal-tensor-coordinates: the existing definition uses ordered shifted Tate lines; the new lemma has no Tate orientation and concerns actual exceptional dualizing objects and etale difference charts.
- All six new nodes vs lem-pur-diagonal-section-pasting: each gives a separate proper subargument; none concludes the parent's global pasting equation together with its open and coordinate assertions. In particular the coordinate-input node does not assert kappa = nu, and the etale-tower node knows no diagonal or section.

The blueprint candidates det-sp-mixed-base-change and det-sp-tower-exceptional-bc concern scalar comparisons and towers, respectively; neither is exceptional-compositor or chart pasting. sk-thm-sf-compatibility is a package-level compatibility assertion, not a replacement for identifying this packet's specified maps. No existing id is overwritten except the dispatched item.

## Mathlib reading

Every new node records the exact queries run through msearch.py, full returned hits and a verdict. Each has grep, Loogle, LeanFinder and an attempted LeanSearch; a second LeanFinder phrasing was used for each. LeanSearch was rate-limited for exchange, diagonal and coherence, and these records say unavailable. A rejected Loogle identifier in the first coherence search is recorded honestly and followed by a valid query. General semantic results covered ring etaleness, pullback geometry, Kahler differentials and generic adjunctions, without any exceptional functor identity stated here.

I read Mathlib/CategoryTheory/Monoidal/Functor.lean:1045, CategoryTheory.Adjunction.isMonoidal_comp: it composes monoidal adjunction structures already given, and neither constructs nor normalizes compact-support exchange. I also read Mathlib/CategoryTheory/Adjunction/CompositionIso.lean:82 and its surrounding composition/associativity definitions. CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv transfers an existing compositor by conjugation; it supplies neither the tensor transpose cocycle nor its geometric etale comparison. Thus neither turns a new node into a one-line Mathlib specialization. The pullback diagonal and standard-smooth results give geometric constituents only; they do not state any of the complete new nodes. The grep results from Hales-Jewett and antidiagonals are unrelated. Existing parent search records were retained unchanged.

## Review by Q95

I read the current chapter and unit records, SETUP's three-level rule and the current main-20261015 composition unit and composition-coherence proof. The precise source for the item and each new node is literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1: the canonical twofold fibre products, standard etale coordinates, pentagon, and the final sentence about smooth-base-change/co-projection factors. That sentence does not itself contain the twelve-step calculation; the retained packet and the six new statements are explicitly agent-written refinements of it. I also read the available etale-locality proof in sec-six-functors-basics/sk-prop-cohsm/lem-pur-co-smooth-etale-locality.proof.md, Step 1, for the normalization of rho, theta and beta. The route remains finite-coefficient and orientation-free, following the prescribed lecture-notes/diagonal route.

For the exchange node I checked the full statements of fix-lem-exchanges, lem-weil-pbc-mate-pasting, thm-sf-comp-composition, def-pur-co-smoothness and thm-pur-cohomological-smoothness. The first supplies horizontal/vertical direct-image exchange equations; mate-pasting clause (2) and the composite counit give exactly the exceptional-compositor identity. The base-change compatibility of the specified theta in cohomological smoothness supplies the tensor equation, rather than an arbitrary isomorphism. In the vertical formula N lives on Z, B_f takes Rg!N, and Ra! takes the mate for g; all domains match. Derived pullback composition and tensor constraints are the two existing derived lemmas, whose full statements I read. The retained termwise argument checks their compatible reassociations rather than assuming an unproved strict equality.

For the double-diagonal node I checked l,r and gf against the actual two Cartesian squares; the beta_f,r target is omega_a, not an unrelated diagonal map. The statement of lem-pur-diagonal-base-change gives exactly alpha as inverse beta restricted along its diagonal. The extra gamma formulas are horizontal transitivity of that same beta. I read the permanence statements for smooth dimension and separated finite-type base change; dimensions remain d,e,d+e and all required arrows are separated finite type. No global separatedness of X,Y,Z was added. The equations i Delta_f=t and j s=Delta_g f are scheme equations induced by the fibre-product universal property, not reasoning solely with points.

For the cocycle/locality node I checked the composition clause of cohomological smoothness, associativity in compact-support composition and reversal of composition under adjunction conjugation. The specified tensor maps therefore supply the sigma cocycle recorded here. I read all three clauses of lem-pur-finite-etale-dualizing-normalization: the mixed etale formula uses its E sigma unit constraint; the beta source-restriction identity has target Le'^* omega_h', and both sides start at Lu_1^* omega_he. A source open is handled by that identity and E, not by falsely calling the source square Cartesian. Locality of expressions, including section pullbacks, is the retained step-7 argument; it does not assume that morphisms in a derived category can be glued from equality on a cover.

For the geometry node I checked the formulas over B=U, their coordinate order, and the genuine Cartesian square R=Q times_(A_B^e) A_B^(d+e). G and H are base changes of the given charts followed by translations; addition is the inverse of subtraction. J is a base change of G. I read lem-weil-pbc-etale-ring-base-change, sbc-lem-affine-space-smooth, def-sbc-affine-space and the actual normal-form statement. The schemes are affine, so the affine ring base-change result used in the retained argument has its hypotheses. The square of F,G is deliberately not asserted Cartesian. The standard affine tower and zero-section equations give the comparisons used to define nu without any Tate trivialization.

For the etale-tower node I checked the three domains explicitly: beta_q,G^-1 goes from omega_qQ to LJ* omega_q; its pullback after E_H,qQ goes from omega_a to LF* omega_q. La* E_G,p ends in La* LG* omega_p. Tensoring these and applying LF* sigma_q,p ends in LF* omega_pq, exactly the target of E_F,pq sigma_a,b. The intermediate equation has the same check before H is inserted. Its retained proof uses the cocycle, the etale-normalization clause (3), and invertible cancellation; it does not conceal a new Cartesian condition.

For the coordinate-identification node I read the full statements of the cited normalization and derived pullback lemmas, the single-diagonal node and the available chart-normalization candidate. H_f and G_g refer to the actual difference charts, not isomorphisms chosen after seeing the desired equality. The first input is identified via beta_a,s^-1, E_H,qQ and beta_q,G^-1, then delta_d. The second starts with beta_pg,f, then E_G,P_e. I checked tau_g's direction against beta_PeV,f and corrected the preliminary draft as described above. For the output, F=JH, Ft=z_(d+e), and normalization under composition identifies the two E routes. The conclusion consists of equalities of maps of derived objects, not merely isomorphisms of cohomology groups.

Assembly step 1 uses exactly the new double-diagonal statement for alpha=(Lt*A)^-1 gamma and its other two versions, the exchange node for D Ll* sigma = sigma(A tensor La*B), and the existing monoidal pullback lemma for Lt* of a tensor. The parent does the cancellation itself; no new node concludes its equation. Assembly step 2 uses the generic cocycle/locality statement, which explicitly includes expressions built from beta, sigma, E, inverse, tensor and section pullbacks. This says precisely what the step uses. Assembly step 3 uses the geometry node for the etale maps, real Cartesian square and Gs/Ft equations; the etale-tower node for its final displayed equation; the input node for both chi equalities and the composite output E; and the derived monoidal comparison to pull the tensor equality to t. The parent carries the final substitution giving chi_gf kappa = nu(chi_f tensor chi_g). The generic smooth lemmas explicitly retain pure relative dimension, so their direct use of the cohomological-smoothness statement needs no extra decomposition by dimension. Every cited statement was opened, and citations.json copies the exact equation or sentence used. No citation relies on an unavailable proof of a node.

I tested all six statements with identity towers, d=e=0 and empty schemes. Identity base changes give identity beta, and the diagonal alpha/gamma formulas reduce to the specified units. For zero coordinate blocks A^0_B=B, translations have no coordinates, and the sigma/E unit removes the corresponding factor without choosing an orientation. If either affine chart is empty every displayed map and Cartesian object still exists, and the section equations are vacuous. Taking G=H=identity in the etale-tower statement recovers sigma_q,p; taking a nontrivial etale chart does not identify its zero fibre with just the diagonal, so no such false Cartesian zero-fibre assertion is present. The derived categories are bounded constructible finite-Tor with the fixed coefficient ring, so omega_g and the tensor inputs are within the domain of the smooth tensor formula. These checks retain all original hypotheses and all finite levels n>=1.

Against delivery-errors B-E, the new nodes introduce their schemes, maps, coefficient category and normalized comparisons independently, have no embedded proof sketches, and cite the notions used. Sources name exact blueprint sentences rather than changing unit route. The six arguments require substantially more than elementary substitution and therefore remain real unsplit items; the parent alone performs elementary cancellation/substitution. They are neither six copies of the conclusion nor one renamed parent. The full original argument remains below for future split workers, including the mixed open restrictions and both coordinate-input calculations. There are no parent dependencies from new nodes, so no new cycle is introduced. The parent has no non-elementary step over 2000 characters; all substantial work was distributed instead of hidden in an oversized assembly step.

The single numbered return request is repaired in full: unchanged statement; six (at least four) new statement-only nodes, including the old local-chart-existence obligation; all original arguments assigned and preserved; parent proof below 3000 characters; genuine logged searches and verbatim citation witnesses; dry run and delivery performed after this self-review. Validation results are appended below when available.

## Retained twelve-step argument, verbatim

This is the complete previous argument, preserved as handoff material rather than put into any new unsplit node's statement. It is not an additional proof field and does not change the short assembly above. The destination labels identify the future worker's obligation.

### Retained step 1 — lem-pur-double-diagonal-section-identifications

Write $r:Q\to Y$ and $l:W\to X$ for the second projections. The universal property [def-pc-fibre-product] gives the commutative diagram with rows $W\xrightarrow aQ\xrightarrow bX$ and $X\xrightarrow fY\xrightarrow gZ$, and vertical arrows $l,r,gf$. Its two squares are Cartesian: $W=Q\times_YX$ and $Q=X\times_ZY$. Its outer rectangle is the base-change square for $gf$, with $ba=p_{gf}$. Evaluation on pairs gives $at=s$, $lt=1_X$, and $rs=f$. Base-change and composition permanence [lem-sbc-smooth-relative-dimension-permanence, lem-pod-separated-finite-type-base-change] give the smooth separated finite-type maps $a,b,ba$ of dimensions $d,e,d+e$. These are the actual two squares used below; no square involving a composition isomorphism is regarded as a square of schemes.

Original uses: def-pc-fibre-product, lem-sbc-smooth-relative-dimension-permanence, lem-pod-separated-finite-type-base-change.

### Retained step 2 — lem-pur-smooth-exceptional-tensor-pasting

Use $B_{h,v,N}:Lu^*Rh^!N\to Rh'^!Lv^*N$ for the transpose of $Lv^*\varepsilon_{h,N}\circ\operatorname{Ex}_!^{-1}$ for a Cartesian square $(h,h',v,u)$; its unit specialization is exactly $\beta_{h,v}$ of [def-pur-co-smoothness]. The horizontal law of [fix-lem-exchanges](2), inverted and followed by the pulled-back counit, gives transitivity of $B$ for successive base changes. The vertical law in the same clause, with compact-support composition [thm-sf-comp-composition], gives
$$c_{b,a,L(gf)^*N}\circ B_{gf,gf,N}=Ra^!(B_{g,gf,N})\circ B_{f,r,Rg^!N}\circ Ll^*c_{g,f,N}.$$ This follows by taking the mates of the two sides of that vertical exchange equation, using [lem-weil-pbc-mate-pasting](2) and the composite counit [def-weil-pbc-composite-adjunction]; conjugation reverses composition as in [def-weil-pbc-adjunction-conjugate]. Thus the geometric exchange equations, as well as the formal mate law, are used.

Original uses: def-pur-co-smoothness, fix-lem-exchanges, thm-sf-comp-composition, lem-weil-pbc-mate-pasting, def-weil-pbc-composite-adjunction, def-weil-pbc-adjunction-conjugate.

### Retained step 3 — lem-pur-smooth-exceptional-tensor-pasting

The tensor and base-change clauses (1),(3) of [thm-pur-cohomological-smoothness] make every displayed $\theta$ and smooth $B$ invertible, and identify $B_{f,r,N}\,Ll^*\theta_{f,N}$ with $\theta_{a,Lr^*N}(1\otimes\beta_{f,r})$. Set
$$A=\beta_{f,r}:Ll^*\omega_f\to\omega_a,\quad B=\beta_{g,gf}:Lr^*\omega_g\to\omega_b,\quad D=\beta_{gf,gf}:Ll^*\omega_{gf}\to\omega_{ba}.$$
Apply the vertical identity of Step 2 at $N=\Lambda$, substitute this tensor compatibility at $N=\omega_g$, and invert $c_{b,a}$. Naturality of $\theta_a$ in $B$ gives exactly
$$D\,Ll^*\sigma_{f,g}=\sigma_{a,b}(A\otimes La^*B).\tag{*}$$
All pullback composition in this formula is supplied by [lem-weil-pbc-proetale-derived-pullback-composition]; [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] supplies its tensor comparison. Their reassociations agree termwise on K-flat flat-term models: both orders send a pure tensor to the same pulled-back tensor, and both composite pullbacks are the termwise canonical module comparison. This also fixes all suppressed associators.

Original uses: thm-pur-cohomological-smoothness, def-pur-co-smoothness, lem-weil-pbc-proetale-derived-pullback-composition, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

### Retained step 4 — lem-pur-double-diagonal-section-identifications

Let $i:W_f\to W$ send $(x,x')$ with $f(x)=f(x')$ to the same pair. Then $(W_f\xrightarrow iW, X\xrightarrow sQ)$ is the base-change square of $a$, and $i\Delta_f=t$. Let $j:Q\to W_g$ send $(x,y)$ to $(f(x),y)$; then $(Q\xrightarrow jW_g,X\xrightarrow fY)$ is the base-change square of $p_g$, and $js=\Delta_gf$. Put $F=\beta_{a,s}:Li^*\omega_a\to\omega_{p_f}$ and $G=\beta_{p_g,f}:Lj^*\omega_{p_g}\to\omega_b$. The comparisons in the statement are
$$\gamma_f=L\Delta_f^*F^{-1}:C_f\to Lt^*\omega_a,\qquad\gamma_g=Ls^*G:Lf^*C_g\to Ls^*\omega_b.$$
Horizontal transitivity from Step 2, applied respectively to the squares for $(f,r)$ then $(a,s)$ and for $(g,g)$ then $(p_g,f)$, gives
$$\alpha_f=(Lt^*A)^{-1}\gamma_f,\quad Lf^*\alpha_g=(Ls^*B)^{-1}\gamma_g,\quad\alpha_{gf}=(Lt^*D)^{-1}.$$
The last formula is precisely [lem-pur-diagonal-base-change] for $gf$ since $lt=1$. The same lemma identifies the first two with the specified $\alpha$, rather than unspecified isomorphisms. Use [lem-weil-pbc-proetale-derived-pullback-composition] throughout to identify the composed pullbacks.

Original uses: def-pc-fibre-product, def-pur-co-smoothness, lem-pur-diagonal-base-change, lem-weil-pbc-proetale-derived-pullback-composition.

### Retained step 5 — assembly step 1

The invertibility in [thm-pur-cohomological-smoothness] and adjunction conjugation [def-weil-pbc-adjunction-conjugate] of [thm-sf-comp-composition] show that each $\sigma$ is an isomorphism. The tensor pullback comparison [lem-weil-pbc-ringed-topoi-derived-tensor-pullback], $at=s$, and derived pullback composition [lem-weil-pbc-proetale-derived-pullback-composition] make $\kappa$ exactly $Lt^*\sigma_{a,b}\circ(\gamma_f\otimes\gamma_g)$. Pull (*) back along $t$, precompose with $\gamma_f\otimes\gamma_g$, and multiply by $(Lt^*D)^{-1}$. The three substitutions of Step 4 give
$$\alpha_{gf}\kappa=\sigma_{f,g}(\alpha_f\otimes Lf^*\alpha_g).$$
This is a calculation with the specified maps, requiring both exchange pasting and base-change compatibility of the tensor map.

Original uses: thm-pur-cohomological-smoothness, thm-sf-comp-composition, def-weil-pbc-adjunction-conjugate, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-proetale-derived-pullback-composition.

### Retained step 6 — lem-pur-dualizing-sigma-cocycle-locality

We will also use the cocycle equation
$$\sigma_{vu,w}(\sigma_{u,v}\otimes1)=\sigma_{u,wv}(1\otimes Lu^*\sigma_{v,w}).\tag{**}$$
This is the tensor-formula composition clause (4) of [thm-pur-cohomological-smoothness] evaluated at $\omega_w$, followed by the inverse exceptional composition comparison: substitute $\sigma_{u,v}=c_{v,u}^{-1}\theta_{u,\omega_v}\mathrm{sym}$ on both sides. Naturality moves $c_{w,v}^{-1}$ through $\theta_u$; clause (4) replaces $\theta_u\circ Lu^*\theta_v$ with the composite tensor map; the two remaining $c$ composites agree because [thm-sf-comp-composition] is associative and conjugation [def-weil-pbc-adjunction-conjugate] reverses the same associative equation. Thus (**) uses the specified $\theta$, not the unspecified isomorphism of the co-smooth-composition lemma. For an etale $u$, [lem-pur-finite-etale-dualizing-normalization](1),(3) say $\sigma_{u,v}^{-1}=E_{u,v}$ after removing $\omega_u$ with $\eta_u$. In particular (**) gives
$$E_{u,wv}\sigma_{vu,w}=Lu^*\sigma_{v,w}(E_{u,v}\otimes1).\tag{***}$$

Original uses: thm-pur-cohomological-smoothness, thm-sf-comp-composition, def-weil-pbc-adjunction-conjugate, lem-pur-finite-etale-dualizing-normalization.

### Retained step 7 — lem-pur-dualizing-sigma-cocycle-locality

Target-open restrictions are Cartesian base changes, so Steps 2-3 and [fix-lem-exchanges](1),(2) identify every restricted $\beta$ and $\sigma$ with the corresponding map on the target open. A further source-open immersion $u$ uses the normalized etale comparison $E_{u,h}$ of [lem-pur-finite-etale-dualizing-normalization], rather than a falsely asserted Cartesian square. Its compatibility with $\sigma$ is (***); its compatibility with the Cartesian base-change maps is Step 2 with the etale normalization of that lemma. Restricting the diagonal pair amounts to restricting both factors, and its diagonal factors through that restriction. Hence applying the derived pullback comparison [lem-weil-pbc-proetale-derived-pullback-composition] and the tensor comparison [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] to the formulas for $\gamma_f,\gamma_g,\kappa$ proves precisely their asserted compatibility with arbitrary compatible source and target open restrictions.

Original uses: fix-lem-exchanges, lem-pur-finite-etale-dualizing-normalization, lem-weil-pbc-proetale-derived-pullback-composition, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

### Retained step 8 — geometry and assembly step 3

For the base $B$ of the statement, [def-sbc-affine-space] and [sbc-lem-affine-space-smooth] give the smooth tower $\mathbf A_B^{d+e}\xrightarrow q\mathbf A_B^e\xrightarrow{P_e}B$. The square with top $\mathbf A_B^{d+e}\to\mathbf A_B^d$ and bottom $P_e$ is Cartesian and $q$ is the pullback of $P_d$. Its $\beta$ gives $Lz_{d+e}^*\omega_q\cong Lz_d^*\omega_{P_d}=D_d$, while $qz_{d+e}=z_e$ gives $Lz_{d+e}^*Lq^*\omega_{P_e}=D_e$ by [lem-weil-pbc-proetale-derived-pullback-composition]. Thus the tensor comparison [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] and $Lz_{d+e}^*\sigma_{q,P_e}$ give the stated $\nu_{d,e}$. Its definition uses no trivialization of any dualizing object.

Original uses: def-sbc-affine-space, sbc-lem-affine-space-smooth, thm-pur-cohomological-smoothness, def-pur-co-smoothness, lem-weil-pbc-proetale-derived-pullback-composition, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

### Retained step 9 — lem-pur-affine-difference-tower-factorization

By Step 7 work on the stated charts and replace $(X,Y,Z)$ by $(U,V,T)$, putting $B=U$. Write $x=(x_1,\ldots,x_d)$ for the chart coordinates of $U\to\mathbf A^d_V$ and $y=(y_1,\ldots,y_e)$ for those of $V\to\mathbf A^e_T$. With $Q=U\times_TV$ and $W=U\times_TU$, define
$$G:Q\to\mathbf A_B^e,\quad(u,v)\mapsto y(v)-y(fu).$$
Put $R=Q\times_{\mathbf A_B^e}\mathbf A_B^{d+e}=\mathbf A_Q^d$ with projections $q_Q:R\to Q$, $J:R\to\mathbf A_B^{d+e}$. Define
$$H:W\to R,\quad(u,u')\mapsto((u,fu'),x(u')-x(u)).$$
Then $a=q_QH$, $b=P_eG$, $qJ=Gq_Q$, and $F=JH$ has the ordered difference coordinates $(x(u')-x(u),y(fu')-y(fu))$. These formulas follow from [def-pc-fibre-product, def-sbc-affine-space]. $G$ is the base change of the chart of $g$, followed by translation by $-y(fu)$; $H$ is the base change of the chart of $f$, followed by translation by $-x(u)$. They are etale by [lem-weil-pbc-etale-ring-base-change]; translation is an isomorphism with inverse addition of the same coordinates. Likewise $J$ is etale as a base change of $G$. All these schemes are affine, so that cited affine ring-base-change statement applies, and all maps are separated finite type. Crucially the square $(W\xrightarrow F\mathbf A_B^{d+e},Q\xrightarrow G\mathbf A_B^e)$ need not be Cartesian; the square defining $R$ is Cartesian. The sections satisfy $Gs=z_e$ and $Ft=z_{d+e}$.

Original uses: def-pc-fibre-product, def-sbc-affine-space, lem-weil-pbc-etale-ring-base-change.

### Retained step 10 — lem-pur-etale-cartesian-tower-tensor-comparison

Write $E$ for the normalized comparisons of [lem-pur-finite-etale-dualizing-normalization]. For the Cartesian square defining $R$, its clause (3) gives
$$E_{J,q}\sigma_{q_Q,G}=\beta_{q,G}^{-1},\tag{a}$$
after identifying $\omega_G$ with the unit. Apply (**) to $(q_Q,G,P_e)$ and (***) to $(J,q,P_e)$. Substitute (a) and $\sigma_{G,P_e}^{-1}=E_{G,P_e}$. Cancellation of the invertible $\sigma_{q_Q,G}$ gives the typed identity
$$E_{J,P_eq}\sigma_{q_Q,b}=LJ^*\sigma_{q,P_e}\bigl(\beta_{q,G}^{-1}\otimes Lq_Q^*E_{G,P_e}\bigr).\tag{b}$$
Both sides have domain $\omega_{q_Q}\otimes Lq_Q^*\omega_b$ and target $LJ^*\omega_{P_eq}$. Now apply (***) with $(H,q_Q,b)$, then pull (b) along $H$. Associativity of $c$ and the etale-composition normalization in that lemma identify $E_{F,P_eq}=LH^*E_{J,P_eq}\circ E_{H,bq_Q}$. Hence
$$E_{F,P_eq}\sigma_{a,b}=LF^*\sigma_{q,P_e}\bigl((LH^*\beta_{q,G}^{-1})E_{H,q_Q}\otimes La^*E_{G,P_e}\bigr).\tag{c}$$
This proves the comparison of the two towers using the Cartesian square and normalized etale factors separately.

Original uses: lem-pur-finite-etale-dualizing-normalization, lem-weil-pbc-proetale-derived-pullback-composition, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

### Retained step 11 — lem-pur-difference-coordinate-section-identifications

Check the input identifications in (c) against those defining $\kappa$. Pull the Cartesian square $(p_f,a,s,i)$ of Step 4 back through $H$. The result is the Cartesian square of etale maps $H:W\to\mathbf A_Q^d$ and $H_f:W_f\to\mathbf A_B^d$, with base $s:B\to Q$; explicitly $H_f(u,u')=(u,x(u')-x(u))$. Its zero section is the image of $\Delta_f$. The base-change compatibility of $\rho$ and $\eta$ in [lem-pur-finite-etale-dualizing-normalization], and vertical exchange pasting [fix-lem-exchanges](2) for $a=q_QH$, identify $L\Delta_f^*E_{H_f,P_d}$ with $Lt^*E_{H,q_Q}\gamma_f$, followed by the base-change comparison for $q_Q$ along $s$. Horizontal exchange pasting identifies that comparison with $Lt^*LH^*\beta_{q,G}^{-1}$ followed by the $D_d$ comparison in Step 8: both are the inverse base-change comparison for $P_d$ along the composite $B\xrightarrow sQ\xrightarrow G\mathbf A_B^e$, with $Gs=z_e$. Thus the first input of $Lt^*$(c) is the actual difference-coordinate identification $C_f\to D_d$, using the route through $\gamma_f$, not an arbitrary isomorphism. For the second input define $G_g:W_g=V\times_TV\to\mathbf A_V^e$ by $(v,v')\mapsto(v,y(v')-y(v))$. The square with top $j:Q\to W_g$ and bottom $f:B\to V$ is Cartesian, as is the square of $G_g$ and $G:Q\to\mathbf A_B^e$ over the affine-space pullback $\mathbf A_B^e\to\mathbf A_V^e$. Vertical exchange pasting for $p_g=P_e^VG_g$, followed by etale beta normalization, identifies the pullback of the section comparison $L\Delta_g^*E_{G_g,P_e^V}$ with $Ls^*E_{G,P_e}\gamma_g:Lf^*C_g\to D_e$. All composed pullbacks here use [lem-weil-pbc-proetale-derived-pullback-composition].

Original uses: lem-pur-finite-etale-dualizing-normalization, fix-lem-exchanges, def-pc-fibre-product, lem-weil-pbc-proetale-derived-pullback-composition.

### Retained step 12 — inputs and assembly step 3

For the output, $Ft=z_{d+e}$ identifies $Lt^*E_{F,P_eq}:C_{gf}\to D_{d+e}$ with the canonical total difference-coordinate comparison; here $E_F$ is obtained by composing the etale comparisons for $H,J$, and [lem-pur-finite-etale-dualizing-normalization](2) makes this the canonical comparison for their composite. Pull (c) back along $t$ and insert $\gamma_f\otimes\gamma_g$. Step 11 identifies its two inputs with $D_d\otimes D_e$ exactly as in Step 8; its middle arrow is $Lz_{d+e}^*\sigma_{q,P_e}$. Its left side is the coordinate image of $\kappa$. This is precisely $\kappa|_U=\nu_{d,e}$. The tensor and pullback comparisons [lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-proetale-derived-pullback-composition] give all the displayed source/target identifications. The statement is conditional on compatible charts; their local availability follows by applying [sbc-thm-etale-local-normal-form] first to $g$ and then to $f$. Empty charts cause no assertion; when either block has length zero the translation, zero section and cocycle calculations have the same formulas with the empty block, including the normalized etale unit. No orientation or Tate-twist comparison has entered.

Original uses: lem-pur-finite-etale-dualizing-normalization, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-proetale-derived-pullback-composition, sbc-thm-etale-local-normal-form.

## Validation

The standalone server check_dag passed. The first full deliver.py --no-push passed preflight at f634e779f4c. After that reading I made pure relative dimensions and the old local-chart-existence obligation explicit in the new statements; the final dry run below validates that completed packet.
