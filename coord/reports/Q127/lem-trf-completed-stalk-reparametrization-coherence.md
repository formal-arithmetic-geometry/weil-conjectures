# Q127 repair report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-completed-stalk-reparametrization-coherence.json: existing statement preserved byte for byte; five-step assembly, 2434 proof-text characters, status split.
- dag/nodes/sec-trace-formula/lem-trf-bounded-quotient-stalk-realization.json: statement, status unsplit; no Mathlib match; no proof or proof dependencies.
- dag/nodes/sec-trace-formula/lem-trf-stalk-compositor-tower-realization.json: statement, status unsplit; no Mathlib match; no proof or proof dependencies.
- dag/nodes/sec-trace-formula/lem-trf-germ-reparametrization-derived-descent.json: statement, status unsplit; no Mathlib match; no proof or proof dependencies.
- dag/nodes/sec-trace-formula/lem-trf-source-section-stalk-cone-comparison.json: statement, status unsplit; no Mathlib match; no proof or proof dependencies.
- citations.json: one verbatim statement quotation for every (assembly step, cited node) pair.
- original-proof.json: verbatim archival copy of the eleven returned proof steps; also reproduced below with their future worker assignments.

## Attachments

None. Searched lean/WeilConjectures/ for the blueprint tag and reparametrization, quotient-stalk and section-restriction terminology. No project declaration there proves the item. Read lean/Sheaf/Paper/CompletedStalkReparametrizationCoherence.lean, including the completed proof docstring and its final theorem: coherence at line 819 has sorry at line 823, and seven preliminary existence/normalization theorems also have sorry. This is reference material, not an attachment. No Lean files were changed and no compiler was invoked.

## WANTED

None. The current blueprint and Stacks sources needed for this extraction are present.

## Return repaired

The return requires at least four independent, comparably sized arguments, delivered statement-only, and an assembly of at most 3000 characters. There were no retained node/report files in this sandbox (only dispatcher .brief markers), so I copied the current returned repository node as the baseline. I preserved its statement, original metadata and existing Lean binding, and extracted exactly four new statements. There was no unchanged re-push. The initial diagnostic invocation exited because the report was not yet present; subsequent validation is run on the completed repair.

The assigned original argument sizes are 2498, 2926, 2949 and 2724 characters, respectively. The parent retains the 1249-character finite-succession/rationalization argument, rewritten as assembly steps 4--5 with the earlier steps available by citation. Nothing in the old proof is silently deleted: all eleven texts and their cited inputs are retained verbatim below. These are instructions for future proofs, not proof steps in the unsplit JSON nodes.

The four statements introduce all schemes, fields, complexes and tower maps. They are intermediate results: the first realizes a stalk as a specific cone; the second pins down compositor coordinates before realization; the third constructs and descends germ tower maps; the fourth proves a chain-map identity before cancellation. None restates the whole parent. The parent still performs realization, cancellation, finite-succession induction and rationalization. No new statement assumes a Weil map or periodic point, and none assumes finite Tor-amplitude.

## Review by Q127

I read coord/brief-stage1.md, stages/1-dag.md, SETUP.md's three blueprint levels, GOAL.md, the whole B--E checklists in both delivery-errors copies, chapter sec-trace-formula and unit sk-thm-trace-transport. The route stays at main-20261015, thm-trf-l-function-euler-product.proof.md, Step 1, Local powers input (b): this is the integral construction whose rationalization that paragraph needs. It does not use the forbidden SGA route.

For the item and the four extracted statements I read sites.tex lemma-point-functor (0F4F), including the formula combining the two colimits and its representative projection, and lemma-point-morphism-sites (05V1); proetale.tex lemma-classical-point (0993) and lemma-pushforward-Noetherian-case (099N), especially (5); and sites-cohomology.tex lemma-derived-limit-is-ok (0941). The Stacks results give the underlying finite point/limit formulas; the simultaneous normalization refinements here are agent arguments, not claims quoted verbatim from Stacks. Each new node's source labels that extraction explicitly. The original proof_origin.by remains agent.

For new node A I checked the full statements of lem-pc-kflat-resolution, def-pur-integral-derived-operations, def-weil-derived-complete-integral-detailed, def-kun-truncations, prop-weil-pbc-proetale-constant-exact, lem-trf-proetale-pullback-stalk-coherence, lem-weil-point-proetale-sections-exact and lem-weil-pbc-ringed-strict-tower-homotopy-limit. Uniformity of [a,b] is a definition hypothesis, not a consequence of individual boundedness. Good truncations act functorially on the actual quotient transitions. Finite pullback is exact for A_n, a finite discrete ring. On the algebraically closed source s, sections are exact and preserve products, so the comparison acts on both cone coordinates. For a=b the retained term is H^a, for the zero complex all maps are the unique zero-object isomorphisms, and unbounded terms of the resolution cause no difficulty. A is not just a truncation lemma available in Mathlib: it includes the specified completed geometric-stalk realization.

For new node B I reread lem-trf-integral-pullback-comparison-realization in full, including eta, the entire-tower counit, the initial completion map with zero shifted coordinate and the associativity/unit clauses. I checked the finite comparison statement (not just its proof) for the displayed germ formula, composition and mixed law. Gamma(chi inverse) has domain J_v(Lf*M), the opposite orientation from chi. The e-coordinate equation is obtained at (v,f,id_s), so its source and target match. The same P tower must be used for all three factors; all nested pullbacks remain constructible by lem-pur-integral-operations-preserve-constructible (1). At f=id or h=id the specified unit gives the identity. The mixed square keeps the order pr_V theta u' delta; it does not commute field automorphisms. B states the strict quotient and counit compatibility that identifies the parent comparisons, rather than replacing the finite lemma.

For new node C I read lem-pur-integral-operations-well-defined and lem-weil-pbc-localization-universal-property, especially clause (2) for natural transformations, together with the finite coherence and geometric-stalk definitions. Chain naturality alone would be insufficient; the statement explicitly includes roofs, independence under the canonical K-flat comparisons and descent preserving composition. Reduction changes only the section x, while reparametrization changes only u, so they commute strictly. R has inverse obtained from delta inverse and its product map acts diagonally on both cone coordinates. For alpha=1 the rule fixes each germ. For two automorphisms Spec reverses their field-map order, hence beta composed with alpha is required even if they do not commute. The empty succession is identity. This is a substantive descent argument, not the elementary two-factor representative computation by itself.

For new node D I read lem-weil-proetale-isomorphism-inverse-image, def-weil-inverse-image-pullback-comparison parts (a),(b), and lem-weil-isomorphism-derived-pullback-comparison-normalization in full. The definition alone does not assert naturality or invertibility, so D cites the normalization theorem for those assertions. The hypothesis N in D^b_c(s,R) includes derived completeness; nothing here asserts invertibility on an incomplete ambient object. Restriction along delta is invertible because delta is an isomorphism; scalar actions use the canonical coefficient isomorphism. For a finite section, the pullback-unit germ has lifts (id_s,delta), hence maps to [s,delta,a]. On Q the specified kappa uses actual quotient maps and a zero shifted component. The identity completion unit and compositor compare this exact whole chain map, not arbitrary maps agreeing on reduction projections. At delta=id this reduces to the actual completion unit. D stops at the chain equality, leaving the parent to cancel Gamma(q) and e_delta.

Assembly step 1 uses A for the whole-cone identification, B for c=Gamma(chi inverse) and its natural specified realization, and C for r and its natural descent. These are the stated conclusions of those nodes. Step 2 uses B's strict composition/unit/mixed equations and C's action equations; realization preserves equations and composition. Step 3 uses D's explicit chain equality and C's formula for r, and uses the actual exact-sections statement to invert Gamma(q) after localization. Step 4 checks the constructibility hypothesis on N=Lv*M using the full clause (1) of lem-pur-integral-operations-preserve-constructible; its induction uses the already proved mixed, binary and section equations, appending one automorphism at a time. Step 5 uses the full definitions of raw rationalization and the point fibre: every morphism is a finite sum of f tensor a and the fibre sends this to a times Gamma(f) tensor E. This proves naturality also for morphisms with denominators; it never assumes they lift to integral morphisms. Inverses and all earlier equations survive this functor.

I checked B1--B10: unsplit nodes have empty proof/proof_deps; notions are introduced or definition-linked; displayed formulas have single TeX escapes; source tags and labels were read; there is no claimed Mathlib leaf; blueprint ancestry and same_as were searched. C1--C8: assembly citations are statements, not hidden proof constructions; no new dependency points back to the item; off-unit exact sections and constructibility are declared generic tools. The extracted nodes' source arguments and their prerequisite lists are preserved below for their next workers. D1--D5: four different intermediate arguments divide all eleven old steps, and no node absorbs the whole proof. E1--E7: checked the finite-ring exactness, algebraically closed point, uniform amplitude, completed domain, map directions and both cone coordinates as described above. No statement dispute or source error was found. The parent statement is exactly unchanged.

No assembly step exceeds 2000 characters. Four comparable proof tasks have been made available to other workers, as required by the return. Search logs include two semantic phrasings per new node, Loogle and Mathlib grep; unknown-identifier Loogle attempts are recorded as invalid and were followed by working substring queries. Hits were read: they concern ordinary/topological or structure-sheaf stalks, abstract localization, truncations or mapping-cocone constructors, not the required specified completed comparisons. General localization remains a cited existing input, not a duplicate new lemma.

## Source argument preservation and assignments

### lem-trf-bounded-quotient-stalk-realization

Original steps 1, 2. This node is statement-only; the following retained argument is for the worker who will split it.

Original step 1 (1209 characters):

Write $R=\mathcal O_E$. Choose a flat-term K-flat representative $P\to M$ and its simultaneous quotient tower $P_n=P\otimes_{\widehat R_T}(A_n)_T$, with actual quotient transitions, by [lem-pc-kflat-resolution] and [def-pur-integral-derived-operations]. The reductions have cohomology in one interval $[a,b]$ by [def-weil-derived-complete-integral-detailed]. To apply the bounded-complex finite stalk theorem, use the functorial zigzag $P_\bullet\leftarrow\tau_{\le b}P_\bullet\to\tau_{\ge a}\tau_{\le b}P_\bullet=:B_\bullet$. Both arrows are levelwise quasi-isomorphisms: the first changes only cohomology above $b$, and the second only below $a$, all of which vanish. Here good truncation uses $\ker d^b$ at the upper endpoint and the quotient by $\operatorname{im}d^{a-1}$ at the lower endpoint (cohomology if $a=b$). These are simultaneous tower constructions because kernels and quotients are functorial. Finite pullback is exact by [prop-weil-pbc-proetale-constant-exact], so it preserves these truncations and quasi-isomorphisms. Thus finite comparisons on the bounded $B_n$ also specify them on $P_n$ through this zigzag. No boundedness of the terms of $P$ or finite Tor-amplitude of $M_n$ is assumed.

Inputs: lem-pc-kflat-resolution, def-pur-integral-derived-operations, def-weil-derived-complete-integral-detailed, prop-weil-pbc-proetale-constant-exact.

Original step 2 (1289 characters):

For an $A_n$-complex $H$ on $s$, identify its identity geometric stalk with $\Gamma(s,H)$: every pointed neighbourhood $(U,u)$ receives the unique pointed map $u:(s,\mathrm{id})\to(U,u)$, and $[U,u,a]\mapsto u^*a$ is inverse to $a\mapsto[s,\mathrm{id},a]$ in the colimit of [def-weil-proetale-geometric-stalk]. Apply [lem-trf-proetale-pullback-stalk-coherence] to $v$ and the identity point to obtain $e_{v,n}:\Gamma(s,v^*P_n)\xrightarrow{\sim}(P_n)_v$. These commute with quotient transitions: a reduction sends the representative section $a$ to its image $\bar a$, and both orders give $[U,u,\bar a]$. Exact point sections [lem-weil-point-proetale-sections-exact] commute with the cone model of [def-pur-integral-derived-operations]: sheaf products have sectionwise products, so evaluation carries $(x_n)\mapsto(x_n-t_nx_{n+1})$ to the identical formula on sections and carries its cone and shift to their module versions. Consequently $J_v(M)$ is canonically the realization of the strict module tower $(P_n)_v$, through these $e_{v,n}$. This is an identification of whole cone complexes. The strict derived-limit functor [lem-weil-pbc-ringed-strict-tower-homotopy-limit] transports the tower quasi-isomorphisms of Step 1, so the bounded replacement does not change this identification.

Inputs: def-weil-proetale-geometric-stalk, lem-trf-proetale-pullback-stalk-coherence, lem-weil-point-proetale-sections-exact, def-pur-integral-derived-operations, lem-weil-pbc-ringed-strict-tower-homotopy-limit.

### lem-trf-stalk-compositor-tower-realization

Original steps 3, 6, 7. This node is statement-only; the following retained argument is for the worker who will split it.

Original step 3 (1201 characters):

Let $\chi_{v,f}:L(fv)^*\to Lv^*Lf^*$ be the specified integral compositor of [lem-trf-integral-pullback-comparison-realization]. Define $c_{f,v,M}=\Gamma(s,\chi_{v,f,M}^{-1})$. The defining map $\eta_{v,f,M}$ of that node identifies $Lv^*Lf^*M$ with realization of the simultaneous tower $v^*f^*P_n$, and identifies this $c$ with the inverse of the finite composition map. More explicitly, in the finite stalk coordinates of Step 2 its map is $e_{fv,n}^{-1}\,c^{\mathrm{fin}}_{f,v,P_n}\,e_{v,f^*P_n}$. Indeed [lem-trf-proetale-pullback-stalk-coherence] applied to $v,f$ and the identity point gives $e_{fv,n}=c^{\mathrm{fin}}_{f,v,P_n}\,e_{v,f^*P_n}\,\Gamma(s,\chi_{v,f,P_n})$. All coefficient transitions commute with this equation by their representative formulas. The integral realization node explicitly uses the counit of the entire reduction tower for $\eta$, and gives independence and naturality of these identifications. Thus this is exactly the required specified comparison, represented on the simultaneous diagrams. All iterated pullbacks remain in $D^b_c$ by [lem-pur-integral-operations-preserve-constructible] (1), so every use of these integral identifications has its required domain.

Inputs: lem-trf-integral-pullback-comparison-realization, lem-trf-proetale-pullback-stalk-coherence, lem-pur-integral-operations-preserve-constructible.

Original step 6 (954 characters):

For $w:s\to Z$ use the same $P_\bullet$ on $X$ for every factor. On each finite level [lem-trf-proetale-pullback-stalk-coherence] gives $c^{\mathrm{fin}}_{fh,w}=c^{\mathrm{fin}}_{f,hw}\,c^{\mathrm{fin}}_{h,w}\,(\chi^{\mathrm{fin}}_{h,f})_w$. The quotient formulas make this an equation of tower maps, as in Step 3. The associativity clause and the entire-tower counit normalization in [lem-trf-integral-pullback-comparison-realization] identify all occurrences of the nested pullbacks with these simultaneous diagrams, including $J_w(\chi_{h,f,M})$. Applying the strict derived-limit functor and exact sections therefore gives precisely $c_{fh,w,M}=c_{f,hw,M}\circ c_{h,w,Lf^*M}\circ J_w(\chi_{h,f,M})$. At the identity morphism the finite comparison is the identity; the unit clause of the integral realization node gives $c_{\mathrm{id},v,M}=1$ under its specified identity identification. This also supplies $J_{\mathrm{id}}(N)=\operatorname{Fib}_sN$.

Inputs: lem-trf-proetale-pullback-stalk-coherence, lem-trf-integral-pullback-comparison-realization, lem-weil-pbc-ringed-strict-tower-homotopy-limit, def-weil-finite-coefficient-point.

Original step 7 (771 characters):

The finite mixed equation is the one in [lem-trf-proetale-pullback-stalk-coherence]. Its representative calculation is explicit: the pullback germ given by $(U,u',V,\theta,a)$ first maps to $[V,\operatorname{pr}_V\theta u',a]$; reparametrization then gives $[V,\operatorname{pr}_V\theta u'\delta,a]$. Reparametrizing $u'$ first and then applying the comparison gives exactly the same representative. Quotient reduction changes only $a$, so the equation holds on the entire strict tower. Under the identifications of [lem-trf-integral-pullback-comparison-realization], these are the maps of Steps 3--4. Functoriality of strict realization therefore gives $r_{fv,\alpha,M}\circ c_{f,v,M}=c_{f,v\delta,M}\circ r_{v,\alpha,Lf^*M}$, as equality of the specified integral maps.

Inputs: lem-trf-proetale-pullback-stalk-coherence, lem-trf-integral-pullback-comparison-realization, lem-weil-pbc-ringed-strict-tower-homotopy-limit.

### lem-trf-germ-reparametrization-derived-descent

Original steps 4, 5, 8. This node is statement-only; the following retained argument is for the worker who will split it.

Original step 4 (935 characters):

For $\delta=\operatorname{Spec}(\alpha)$ define the tower map $R_{v,\alpha,n}:(P_n)_v\to(P_n)_{v\delta}$ by $[U,u,a]\mapsto[U,u\delta,a]$. The finite comparison node [lem-trf-proetale-pullback-stalk-coherence] supplies this natural $A_n$-linear isomorphism on bounded complexes. It is also a strict tower map: reducing the section before or after this operation gives $[U,u\delta,\bar a]$. Its inverse is the same construction with $\delta^{-1}$, and therefore is a strict inverse. Transport its realization through the Step 2 identifications to define $r_{v,\alpha,M}$. Concretely a map $R_\bullet$ of towers gives the cone map $(b,a)\mapsto((\prod R_n)b,(\prod R_n)a)$; commuting with transitions makes this a chain map. Thus the construction specifies both coordinates of the cone, not just maps on reductions. Functoriality of strict derived limit [lem-weil-pbc-ringed-strict-tower-homotopy-limit] makes it an integral isomorphism.

Inputs: lem-trf-proetale-pullback-stalk-coherence, lem-weil-pbc-ringed-strict-tower-homotopy-limit.

Original step 5 (1140 characters):

The constructions are natural for every integral derived morphism, including ones not represented by a single map between the initially chosen resolutions. On chain maps the representative formulas for $e$, $c^{\mathrm{fin}}$ and $R$ are natural, and hence natural on the whole quotient diagram. The descent and resolution comparisons of [lem-pur-integral-operations-well-defined] identify the quotient-cone constructions from different K-flat representatives. Exact point sections preserve quasi-isomorphisms by [lem-weil-point-proetale-sections-exact]. Thus these chain functors invert the arrows used to represent derived morphisms. The localization universal property [lem-weil-pbc-localization-universal-property] (2) descends their natural transformations uniquely, preserving identities and composition; naturality for the inverse of a quasi-isomorphism follows by multiplying its naturality square by its inverses. This proves resolution independence of $r$ as well as naturality for roofs. For $c$ it agrees with the already natural, resolution-independent $\eta$-construction of [lem-trf-integral-pullback-comparison-realization].

Inputs: lem-pur-integral-operations-well-defined, lem-weil-point-proetale-sections-exact, lem-weil-pbc-localization-universal-property, lem-trf-integral-pullback-comparison-realization.

Original step 8 (874 characters):

The action law is an equality on representatives in [def-weil-proetale-geometric-stalk]: successive reparametrizations send $[U,u,a]$ to $[U,u\delta,a]$ and then $[U,u\delta\epsilon,a]$, while a single reparametrization by $\delta\epsilon$ gives that same representative. Also $\operatorname{Spec}(\alpha)\circ\operatorname{Spec}(\beta)=\operatorname{Spec}(\beta\circ\alpha)$, because affine spectrum reverses ring-map composition. Identity reparametrization fixes every representative. These are strict tower equations, and the product maps on both cone coordinates obey the same composition law. Hence $r_{v\delta,\beta,M}\circ r_{v,\alpha,M}=r_{v,\beta\circ\alpha,M}$ and $r_{v,1,M}=1$. Induction on the number of automorphisms proves the finite-succession assertion: appending one automorphism uses this two-factor identity, with the zero-length succession the identity.

Inputs: def-weil-proetale-geometric-stalk.

### lem-trf-source-section-stalk-cone-comparison

Original steps 9, 10. This node is statement-only; the following retained argument is for the worker who will split it.

Original step 9 (1189 characters):

For a complex $N$ on $s$, let $\rho_{\delta,N}:\Gamma(s,N)\to\Gamma(s,\delta^{-1}N)$ be restriction along $\delta$, followed by inverse-image insertion. The site-equivalence formula of [lem-weil-proetale-isomorphism-inverse-image] identifies the target with sections of $N$ over $(s\xrightarrow{\delta}s)$; restriction along the isomorphism $\delta$ has inverse restriction along $\delta^{-1}$, so $\rho$ is an isomorphism. The specified map of the question is $j_{\delta,N}=\Gamma(s,\kappa^\delta_N)\rho_{\delta,N}$. For integral constructible $N$, [lem-weil-isomorphism-derived-pullback-comparison-normalization] says this SPECIFIED $\kappa$ is natural and invertible and is the quotient-cone map with zero shifted coordinate. Its hypothesis holds since $N\in D^b_c(s,R)$ is derived complete. For a finite-coefficient sheaf, a section $a\in N(s)$ under restriction, insertion and $\kappa$ is the pullback-unit germ with source lift $\mathrm{id}_s$ and target lift $\delta$. The finite comparison formula sends it to $[s,\delta,a]$. This is also $r^{\mathrm{fin}}_{\mathrm{id},\alpha}([s,\mathrm{id},a])$. This proves the section equation at finite level directly from the normalizations.

Inputs: lem-weil-proetale-isomorphism-inverse-image, def-weil-inverse-image-pullback-comparison, lem-weil-isomorphism-derived-pullback-comparison-normalization, def-weil-derived-complete-integral-detailed, lem-trf-proetale-pullback-stalk-coherence.

Original step 10 (1535 characters):

Use one flat-term K-flat $Q\xrightarrow{q}N$ and $Q_n$ for all factors. Let $\mathcal H_v=\operatorname{Cone}(1-s:\prod_n(Q_n)_v\to\prod_n(Q_n)_v)[-1]$, and let $e_v:J_v(N)\xrightarrow{\sim}\mathcal H_v$ be the whole-cone identification of Step 2. For $v=\mathrm{id}$ its source is $\Gamma(s,N)$ via Step 6. The normalization theorem [lem-weil-isomorphism-derived-pullback-comparison-normalization], with $g=\mathrm{id}$, identifies $e_{\mathrm{id}}$ with sections of the actual completion unit, followed by the identity-stalk identifications; this unit is invertible on the derived-complete domain. Thus $e_{\mathrm{id}}\Gamma(q)$ sends $z$ to $(0,([s,\mathrm{id},\bar z_n])_n)$. By [def-weil-inverse-image-pullback-comparison], $j_{\delta,N}\Gamma(q)$ uses these same reductions, restricted along $\delta$, with zero shifted coordinate. Step 9 and the specified compositor realization [lem-trf-integral-pullback-comparison-realization] therefore give
$$e_\delta c_{\delta,\mathrm{id},N}j_{\delta,N}\Gamma(q)(z)=(0,([s,\delta,\bar z_n])_n)=\operatorname{Cone}(R_{\mathrm{id},\alpha,\bullet})e_{\mathrm{id}}\Gamma(q)(z).$$
These are equal chain maps on $\Gamma(s,Q)$, including the shifted coordinate. Exact sections [lem-weil-point-proetale-sections-exact] make $\Gamma(q)$ an isomorphism after localization. Cancel it and $e_\delta$; the definition of $r$ in Step 4 now gives $c_{\delta,\mathrm{id},N}j_{\delta,N}=r_{\mathrm{id},\alpha,N}$. This proves equality of the specified maps without using detection by reduction projections.

Inputs: lem-weil-isomorphism-derived-pullback-comparison-normalization, def-weil-inverse-image-pullback-comparison, lem-trf-integral-pullback-comparison-realization, lem-weil-point-proetale-sections-exact.

### Parent assembly: original step 11

Apply Step 10 to $N=Lv^*M$, which is constructible by [lem-pur-integral-operations-preserve-constructible] (1). The mixed equation of Step 7 and the compositor identity of Step 6 allow each occurrence of a source automorphism to pass through $c_{f,v}$ with exactly the displayed reparametrized point. For successive automorphisms, replace each $c_{\delta,\mathrm{id}}j_\delta$ by $r$ using Step 10, then combine adjacent $r$'s by Step 8. This proves compatibility with any finite succession and with the comparison for any $v$. All constructions are $R$-linear, since the finite maps preserve scalar multiplication and products, cones and sections carry the induced $R$-action. Finally use [def-weil-rationalization-karoubi] and [def-weil-finite-coefficient-point]: on objects rationalization uses the same integral representatives, and on morphisms $f\otimes a$ the fiber map is $a(\Gamma(s,f)\otimes E)$. Send the integral comparison families and their equalities through these functors. Naturality for arbitrary rational morphisms follows by this formula and linearity, first for a simple tensor and then for a finite sum. Inverses remain inverses. This gives all assertions for $E$, with no Weil datum or integrality assumption on the morphisms.

Inputs: lem-pur-integral-operations-preserve-constructible, def-weil-rationalization-karoubi, def-weil-finite-coefficient-point.

## Not duplicates

The whole DAG and imported blueprint were searched by reparametrization, quotient stalk, stalk comparison and section comparison, and by the Stacks tags. The blueprint hits are the finite local-Frobenius conjugacy input and an orientation-chart section comparison, not these completed maps. The nearest blueprint ancestor is thm-trf-l-function-euler-product, through the item and lem-trf-rational-local-frobenius-powers. Below are all same-tag pairs (including incidental mentions), followed by the closest additional conceptual pairs.

lem-trf-bounded-quotient-stalk-realization vs det-pe-topos-functoriality-site: the existing statement concerns The pro-étale site is subcanonical and its sheaves form a topos; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs def-weil-pbc-topos: the existing node defines Grothendieck topos: small-site presentation; this is a theorem which proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-coef-infinity-section-cylinder-cocone: the existing statement concerns Lifting a cocone through a right fibration is a path in its section space; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-sf-point-ringed-evaluation-model: the existing statement concerns Ringed geometric-point evaluation with signed tensor and coefficient models; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-trf-nearby-proper-hyperdescent: the existing statement concerns Truncated nearby-cycle descent along a proper hypercover; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-trf-log-smooth-log-regular: the existing statement concerns Injective logarithmic charts preserve log regularity and recover divisorial structure; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-trf-finite-scheme-derived-germs: the existing statement concerns Derived germs and pullback units on a finite geometric scheme; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-trf-completed-stalk-reparametrization-coherence: the parent asserts integral and rational coherence jointly; this new intermediate result proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-trf-rational-local-frobenius-powers: the existing statement concerns Rational stalk Frobenius powers along a closed-point orbit; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-trf-local-frobenius-conjugacy: the existing statement concerns Conjugacy of the local Frobenius along the Frobenius orbit; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-trf-proetale-pullback-stalk-coherence: the existing statement is finite-coefficient bounded-complex coherence; this extraction proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs thm-trf-coefficient-morphism-trace-formula: the existing statement concerns Trace formula for Frobenius coefficient morphisms over a finite ring; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-pc-localized-tensor-comparison-closure-triangles: the existing statement concerns Localized tensor comparison closure: Triangle; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-pc-localized-tensor-comparison-closure-coproducts: the existing statement concerns Localized tensor comparison closure: Coproduct; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-pc-localized-tensor-comparison-closure-retracts: the existing statement concerns Localized tensor comparison closure: Retract; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-pc-localized-tensor-comparison-closure: the existing statement concerns Localizing closure of the tensor comparison predicate; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-sfb-intrinsic-finite-derived-pullback: the existing statement concerns Intrinsic finite-coefficient derived pullback preserves bounded constructibility; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-sfb-profinite-action-finite-quotients: the existing statement concerns Finite equivariant quotient presentations of profinite actions; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-weil-pbc-ringed-localization-rhom-calculus: the existing statement concerns Derived internal Hom and localization of a bounded localization complex; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-pe-comparison-reflects-local-torsion: the existing statement concerns Etale/pro-etale comparison reflects local integer torsion; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-cbc-proetale-sheafification-geometric-stalk: the existing statement concerns Sheafification preserves ordinary pro-etale geometric stalks; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-cbc-proetale-extension-zero: the existing statement concerns Extension by zero on the pro-etale site; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-cbc-proetale-classical-stalk: the existing statement concerns Classical pro-etale stalks: strict localization and exactness; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-cbc-proetale-stalk-conservative: the existing statement concerns Detecting isomorphisms on the pro-etale site; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-pur-lisse-uniqueness: the existing statement concerns Uniqueness for lisse sheaf maps; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-cbc-proetale-comparison-stalk: the existing statement concerns Geometric stalks commute with etale-to-pro-etale inverse image; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-pur-proetale-inverse-image-stalk: the existing statement concerns Geometric stalks commute with pro-etale inverse image; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-bounded-quotient-stalk-realization vs lem-sc-reciprocal-cover-line-bundle: the existing statement concerns Two sections of a line bundle glued from reciprocal functions; the new statement instead proves the normalized completed geometric-stalk quotient-cone realization and simultaneous bounded truncations for every v and M.

lem-trf-stalk-compositor-tower-realization vs lem-trf-completed-stalk-reparametrization-coherence: the parent asserts integral and rational coherence jointly; this new intermediate result identifies the specified integral compositor in finite germ coordinates on whole quotient diagrams, with composition and mixed squares.

lem-trf-stalk-compositor-tower-realization vs lem-trf-rational-local-frobenius-powers: the existing statement concerns Rational stalk Frobenius powers along a closed-point orbit; the new statement instead identifies the specified integral compositor in finite germ coordinates on whole quotient diagrams, with composition and mixed squares.

lem-trf-stalk-compositor-tower-realization vs lem-trf-local-frobenius-conjugacy: the existing statement concerns Conjugacy of the local Frobenius along the Frobenius orbit; the new statement instead identifies the specified integral compositor in finite germ coordinates on whole quotient diagrams, with composition and mixed squares.

lem-trf-stalk-compositor-tower-realization vs lem-trf-proetale-pullback-stalk-coherence: the existing statement is finite-coefficient bounded-complex coherence; this extraction identifies the specified integral compositor in finite germ coordinates on whole quotient diagrams, with composition and mixed squares.

lem-trf-stalk-compositor-tower-realization vs lem-cbc-site-point-comap-germ: the existing statement concerns Site-point inverse-image comparison with its unit-germ formula; the new statement instead identifies the specified integral compositor in finite germ coordinates on whole quotient diagrams, with composition and mixed squares.

lem-trf-stalk-compositor-tower-realization vs lem-pur-proetale-inverse-image-stalk: the existing statement concerns Geometric stalks commute with pro-etale inverse image; the new statement instead identifies the specified integral compositor in finite germ coordinates on whole quotient diagrams, with composition and mixed squares.

lem-trf-germ-reparametrization-derived-descent vs lem-coef-space-universal-colimits: the existing statement concerns Universality of colimits of spaces; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-coef-exponential-dependent-product-representation: the existing statement concerns The exponential pullback represents maps over an object; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-coef-infinity-iterated-slice-mapping: the existing statement concerns Mapping spaces in an iterated coherent slice; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs def-coef-space-base-change: the existing node defines Coherent space slices and base-change functors; this is a theorem which constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-trf-completed-stalk-reparametrization-coherence: the parent asserts integral and rational coherence jointly; this new intermediate result constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-trf-rational-local-frobenius-powers: the existing statement concerns Rational stalk Frobenius powers along a closed-point orbit; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-trf-local-frobenius-conjugacy: the existing statement concerns Conjugacy of the local Frobenius along the Frobenius orbit; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-trf-proetale-pullback-stalk-coherence: the existing statement is finite-coefficient bounded-complex coherence; this extraction constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-sfb-intrinsic-finite-derived-pullback: the existing statement concerns Intrinsic finite-coefficient derived pullback preserves bounded constructibility; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-sfb-site-finitary-slice-enough-points: the existing statement concerns Enough points from a cover by finitary slices; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-weil-pbc-finite-etale-unit-stalk-inclusion: the existing statement concerns Finite etale reverse-adjunction unit includes a geometric stalk summand; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-weil-pbc-sets-etale-inverse-image-stalk-germ: the existing statement concerns Stalk of the etale inverse image of a sheaf of sets, with germs; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-weil-pbc-inverse-image-stalk-germ: the existing statement concerns Stalk of an inverse image, compatible with germs of pulled-back sections; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-weil-pbc-etale-section-zero-neighbourhood: the existing statement concerns A zero neighbourhood for an etale section killed by inverse image; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-pur-lisse-uniqueness: the existing statement concerns Uniqueness for lisse sheaf maps; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-cbc-site-point-comap-germ: the existing statement concerns Site-point inverse-image comparison with its unit-germ formula; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-cbc-proetale-comparison-stalk: the existing statement concerns Geometric stalks commute with etale-to-pro-etale inverse image; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-germ-reparametrization-derived-descent vs lem-pur-proetale-inverse-image-stalk: the existing statement concerns Geometric stalks commute with pro-etale inverse image; the new statement instead constructs source-automorphism germ tower maps at arbitrary geometric points and descends their action to all integral derived morphisms.

lem-trf-source-section-stalk-cone-comparison vs lem-trf-completed-stalk-reparametrization-coherence: the parent asserts integral and rational coherence jointly; this new intermediate result identifies restriction/insertion with the reparametrized germ on BOTH completed cone coordinates for every source automorphism.

lem-trf-source-section-stalk-cone-comparison vs lem-trf-rational-local-frobenius-powers: the existing statement concerns Rational stalk Frobenius powers along a closed-point orbit; the new statement instead identifies restriction/insertion with the reparametrized germ on BOTH completed cone coordinates for every source automorphism.

lem-trf-source-section-stalk-cone-comparison vs lem-trf-local-frobenius-conjugacy: the existing statement concerns Conjugacy of the local Frobenius along the Frobenius orbit; the new statement instead identifies restriction/insertion with the reparametrized germ on BOTH completed cone coordinates for every source automorphism.

lem-trf-source-section-stalk-cone-comparison vs lem-trf-proetale-pullback-stalk-coherence: the existing statement is finite-coefficient bounded-complex coherence; this extraction identifies restriction/insertion with the reparametrized germ on BOTH completed cone coordinates for every source automorphism.

lem-trf-source-section-stalk-cone-comparison vs lem-cbc-site-point-comap-germ: the existing statement concerns Site-point inverse-image comparison with its unit-germ formula; the new statement instead identifies restriction/insertion with the reparametrized germ on BOTH completed cone coordinates for every source automorphism.

lem-trf-source-section-stalk-cone-comparison vs lem-pur-proetale-inverse-image-stalk: the existing statement concerns Geometric stalks commute with pro-etale inverse image; the new statement instead identifies restriction/insertion with the reparametrized germ on BOTH completed cone coordinates for every source automorphism.

lem-trf-bounded-quotient-stalk-realization vs lem-trf-point-sections-completion-cone: the existing general cone/sections assertion is reused as a notion, but its completed specialization is at s and geometric Frobenius; A additionally compares arbitrary geometric stalks on T and uniformly bounded quotient-tower replacements.

lem-trf-bounded-quotient-stalk-realization vs def-trf-point-sections-roos-comparison: the existing definition specifies sectionwise product/cone coordinates only; A identifies these coordinates with completed pullback stalks and bounded quotient models.

lem-trf-bounded-quotient-stalk-realization vs lem-sf-point-ringed-evaluation-model: the existing theorem compares ordinary ringed-point tensor products; A compares completed geometric pullback with its quotient-stalk inverse limit.

lem-trf-stalk-compositor-tower-realization vs lem-trf-integral-pullback-comparison-realization: the existing theorem supplies scheme-pullback compositors eta/chi and their normalization; B identifies their application under point sections with specific finite stalk-germ maps.

lem-trf-germ-reparametrization-derived-descent vs lem-trf-point-system-transport-descent: the existing theorem treats restriction/insertion of Frobenius powers on systems at s; C treats reindexing arbitrary pointed neighbourhoods for any v on T and any field automorphism.

lem-trf-germ-reparametrization-derived-descent vs lem-trf-point-system-roos-transport: the existing theorem compares Frobenius restriction with whole-system realization at s; C gives the independent geometric-stalk action and K-flat model descent for arbitrary source automorphisms.

lem-trf-source-section-stalk-cone-comparison vs lem-weil-point-automorphism-restriction-natural: the existing theorem provides natural linear restriction/insertion before completed pullback; D adds the specified kappa and compositor and identifies the resulting map with reparametrized stalk germs on both cone coordinates.

lem-trf-source-section-stalk-cone-comparison vs lem-weil-isomorphism-derived-pullback-comparison-normalization: the existing theorem normalizes kappa via the completion unit; D applies the finite stalk comparison to that normalized map and proves its exact section/germ identity.

lem-trf-source-section-stalk-cone-comparison vs lem-trf-completion-unit-strict-quotient-model: the existing theorem identifies the actual completion unit with its augmentation; D compares that augmentation after source restriction and the stalk compositor with a different, germ-reparametrized chain map.

## Unfinished work

No unfinished repair action. The four new nodes deliberately remain unsplit and unproved for parallel stage-1 work. Their statements, searches, sources and all retained proof arguments are delivered here. This report does not claim a Lean proof.
