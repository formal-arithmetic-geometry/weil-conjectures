# Q128 stage-1 repair report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-local-frobenius-transport-normalization.json`: parent split, statement unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-finite-return-frobenius-cancellation.json`: statement, unsplit; no Mathlib match; no proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-local-normalization-strict-realization.json`: statement, unsplit; no Mathlib match; no proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-iterated-return-transport-scalar-calculus.json`: statement, unsplit; no Mathlib match; no proof steps.

## Attachments

None. `WeilConjectures.localFrobeniusTransportNormalization` in `lean/Sheaf/Paper/LocalFrobeniusTransportNormalization.lean:1030` ends in `sorry` at line 1037. Searches by blueprint tag and notion in `lean/WeilConjectures/` found no declaration supplying the complete item. Related Weil-sheaf stalk-transport results concern different coefficient models and do not assert the specified strict-system comparisons.

## WANTED

None: the blueprint source and Stacks source required for this repair are present locally.

## Return repaired

The returned node carries ten proof steps totaling 11515 characters. The sandbox initially contained only dispatcher brief markers, so the current shared node supplies the returned text; no previous sandbox report, citations or search log existed. I preserved the parent statement, Lean record, blueprint provenance, import fields and historical review records. The three new independent statement-only tasks distribute actual arguments: finite cancellation (old 1,3,4), strict-system realization and rationalization (old 5,6,7), and iterated naturality plus scalar comparison calculus (old 2,8,9). The parent retains old 10 as the explicit substitution. They have no dependencies on each other or the parent, so all three can start separately. The complete old arguments are retained verbatim below, including their citations, for the next workers; they are not proof sketches hidden in the unsplit node statements.

## What was wrong

The return identifies excessive proof size, not a statement error. No statement correction or route change was required. The new statements expose the actual maps, chain-level versus derived equalities, hypotheses, and associators used by the old proof. The strict-realization node is conditional on the finite chain identity: it does not subsume finite cancellation. The scalar-calculus node gives the two intermediate equations, not the final local coefficient equation. Thus the parent still performs a mathematical assembly.

## Not finished

Proofs of the three extracted statements are deliberately left unsplit for parallel workers, as explicitly required by the return. No Lean was written and no compiler, Lake, build, or local preflight was run.

## Review by Q128

I read the item and its current blueprint ancestor `prop-trf-karoubi-independence.proof.md` (last sentence), the trace-transport unit and trace-formula chapter. The ancestor only specifies the transport goal; the detailed local arguments are agent-written, as recorded by the original proof origin. I read Stacks Tag 0F6W in `literature/stacks-project/more-morphisms.tex`, label `lemma-relative-frobenius-weakly-etale`: it asserts that relative Frobenius of a weakly etale map is an isomorphism, and does not itself assert the final-object normalization. The latter calculation is explicitly part of the finite cancellation task, not falsely attributed to that tag. I read the statements of every old proof dependency and the candidate duplicate nodes discussed below.

For the finite task I checked the inverse convention in `def-weil-frobenius-detailed`, the specified rational-point summand in `thm-trf-frobenius-fixed-points`, and the factorization in `prop-trf-frobenius-factorization`. The identity of absolute Frobenius with the composite uses geometric Frobenius, not the arithmetic one. `lem-pur-frobenius-trivialization-pullback` specifies the relative-Frobenius normalization and the pullback equation; it does not by itself give the final-object computation, which remains assigned to the new task. `lem-weil-proetale-isomorphism-inverse-image` gives evaluation after reindexing the site, and exact constant pullback and point sections justify termwise computation. The new finite statement includes chain-map equality and the return equations, precisely what parent Steps 1 and 2 take from it.

For the realization task I checked that `lem-pc-kflat-resolution` gives flat terms and `lem-pur-kflat-change-of-rings` preserves K-flatness after nonflat quotients. `lem-trf-scheme-galois-coefficient-change` covers arbitrary finite coefficient homomorphisms without Tor restrictions; `lem-trf-point-sections-finite-reduction` assumes bounded-above cohomology, supplied by the bounded reductions in `def-weil-derived-complete-integral-detailed`. `lem-trf-integral-point-transport-tower-realization` identifies the specified integral map through the whole quotient tower; `lem-trf-integral-pullback-comparison-realization` specifies the actual composition families. `lem-weil-pbc-ringed-strict-tower-homotopy-limit` supplies a functor on whole tower morphisms, not faithfulness of individual evaluations. The new task asserts the necessary transition coherence and realization identifications; the parent applies it to the finite chain identity, never inferring equality from separate derived reductions. Rationalization preserves the same objects and tensors morphisms, so arbitrary rational morphisms require the additivity argument in old Step 7, retained below.

For the scalar task I checked `lem-weil-frobenius-point-transport-natural` clause (2), including its one-step scalar compatibility, against the induction in old Steps 2 and 9. The iteration is successive one-step transport, not a newly chosen map for a power. The specified composition/scalar equation, equality-of-map compatibility and arbitrary-iteration clauses of `lem-trf-integral-pullback-comparison-realization` are exactly the inputs for old Step 8. The scalar task states its return-square equation and its iterated point equation explicitly. Parent Step 3 uses those equations and their naturality, and the natural point-sections comparison from `lem-weil-point-sections-scalar-extension`; expanding $b$, substituting both equations and applying naturality of $I$ yields the required equation. The last step is elementary substitution after citing these inputs, not an uncited transport theorem. The parent uses the same $U$ notation for point pullback as the new statements.

I checked $m=1$, a nonminimal positive period, the zero complex, a constant rank-one coefficient sheaf, and $E=M$. In rank one restriction and the canonical trivialization give the identity; an arbitrary scalar multiple would fail this test. Identity scalar comparison and the prescribed tensor associator give the identity-extension and three-field cases. For the empty scheme there is no chosen rational point, so that case is vacuous. A bounded reduction need not be perfect; none of the new statements imposes a perfectness or finite Tor-amplitude hypothesis. I checked source locations, self-contained objects, TeX escaping, empty child proof fields, statement dependencies, absence of back-edges to the parent, and exact statement quotations in `citations.json` against B–E of the delivery-errors checklist. The only correction relative to the returned proof is its granularity: the parent statement is unchanged.

## Preserved returned argument and allocation

### lem-trf-finite-return-frobenius-cancellation

Assigned returned steps: 1, 3, 4.

**Old Step 1.** Write $g=g_X$, $h=g_s^m$, $H=\operatorname{Fr}^{(q^m)}_X$ and $r=\operatorname{Fr}^{(q^m)}_s=h^{-1}$. The last equality follows from the arithmetic/geometric inverse convention in [def-weil-frobenius-detailed]. By [thm-trf-frobenius-fixed-points], the $k$-point $\bar y$ obtained from the specified rational point satisfies $\Phi^m\bar y=\bar y$. The factorization [prop-trf-frobenius-factorization] and the inverse convention give $\Phi^m=g^mH$. Absolute Frobenius is natural: on affine rings this is the identity $f(a^{q^m})=f(a)^{q^m}$, so $H\bar y=\bar y r$. Therefore $g^m\bar y r=\bar y$, and composition with $h$ gives $g^m\bar y=\bar y h$. These are equalities of scheme maps; semilinear $g$ is not being treated as a $k$-morphism.

Cited statements: def-weil-frobenius-detailed, thm-trf-frobenius-fixed-points, prop-trf-frobenius-factorization.

**Old Step 3.** At finite coefficients the point calculation can be made on a sheaf $N$, then degreewise on a complex. By [lem-weil-proetale-isomorphism-inverse-image](1), $(Lh^*N)(s)=N(s\xrightarrow{h}s)$. Under this identification, restriction followed by colimit insertion in [def-weil-frobenius-point-transport] is $\operatorname{res}_h:N(s,1)\to N(s,h)$; composing $m$ such maps is restriction along $h=g_s^m$. Let $\tau_s:Lr^*\to1$ be the canonical absolute-Frobenius trivialization specified by [lem-pur-frobenius-trivialization-pullback], with exponent $am$. At the final object its value on a sheaf $M$ is $(\operatorname{res}_r^M)^{-1}$: the relative-Frobenius identification in that statement, adjointed to inverse image and evaluated at the final object, is the inverse of restriction along the isomorphism $r:(s,r)\to(s,1)$. For $M=Lh^*N$, this restriction identifies with $\operatorname{res}_r:N(s,h)\to N(s,1)$; its inverse is $\operatorname{res}_h$. Thus under $Lr^*Lh^*N\cong N$ one has $\Gamma(s,\tau_{s,Lh^*N})=I_N^{(m)}$. Exact constant-coefficient pullback [prop-weil-pbc-proetale-constant-exact] and exact point sections [lem-weil-point-proetale-sections-exact] make this a degreewise identity computing the derived maps. No scalar is inserted.

Cited statements: lem-weil-proetale-isomorphism-inverse-image, def-weil-frobenius-point-transport, lem-pur-frobenius-trivialization-pullback, prop-weil-pbc-proetale-constant-exact, lem-weil-point-proetale-sections-exact.

**Old Step 4.** Expand the canonical comparison specified in the statement: with $\tau_X:LH^*\to1$, it is $\kappa_K^{(m)}=(\tau_X)_{L(g^m)^*K}\circ c_{H,g^m,K}$, where $c_{H,g^m}:L\Phi^{m*}\to LH^*L(g^m)^*$ is the canonical composition map. This is the cancellation of absolute Frobenius in $\Phi^m=g^mH$ from [prop-trf-scheme-galois-comparison], with its required canonical normalization. Apply the pullback-naturality equation of [lem-pur-frobenius-trivialization-pullback] to $u=\bar y$ and exponent $am$. It identifies $P_\Lambda(\tau_X)$ with $\tau_sP_\Lambda$ under $H\bar y=\bar y r$. Use [lem-weil-pbc-proetale-derived-pullback-composition] to identify the successive pullbacks. After precomposition with the fixed-point identification $\rho_{y,m,K}$, the resulting map is $\Gamma(s,\tau_{s,P_\Lambda L(g^m)^*K})$ with source identified with $P_\Lambda K$ through $Lr^*H_\Lambda^m\cong1$ and $v_{\Lambda,K}$. Naturality of $\tau_s$ with respect to $v_{\Lambda,K}$ and Step 3 give
$$J_{y,\Lambda}(\kappa_K^{(m)})\rho_{y,m,K}=\operatorname{Fib}_s(v_{\Lambda,K})I^{(m)}_{P_\Lambda K}=t_{y,m,K}.$$
Here the canonical composition identifications on the two paths agree: on a pullback of a section both send it to the same section on the iterated fiber product, with its same projections. The termwise description in the cited composition statement computes those identifications.

Cited statements: prop-trf-scheme-galois-comparison, lem-pur-frobenius-trivialization-pullback, lem-weil-pbc-proetale-derived-pullback-composition.

### lem-trf-local-normalization-strict-realization

Assigned returned steps: 5, 6, 7.

**Old Step 5.** The equality of Step 4 holds before localizing complexes. For an integral object choose one flat-term K-flat resolution $Q\to K$ by [lem-pc-kflat-resolution] and use the simultaneous quotients $Q_n=Q\otimes(A_{E,n})_X$. They are K-flat with flat terms by [lem-pur-kflat-change-of-rings]. Every restriction used in Step 3, every colimit coprojection, and the relative-Frobenius isomorphisms specifying $\tau$ is a natural map of module sheaves, hence commutes with $Q_{n+1}\to Q_n$. The coefficient factors send a tensor $x\otimes b$ to the restriction of $x$ tensored with $b$; reduction before or after this map therefore gives the same tensor. The termwise pullback-composition maps of [lem-weil-pbc-proetale-derived-pullback-composition] have the same property. Consequently Step 4 is an equality of maps of these strict quotient diagrams, including their transitions. For derived change of the finite coefficient ring, [lem-trf-scheme-galois-coefficient-change] gives the equation for the specified $\kappa^{(m)}$, with no flatness or Tor-amplitude assumption; the point comparison [lem-trf-point-sections-finite-reduction] applies because every reduction of an integral constructible object is bounded by [def-weil-derived-complete-integral-detailed]; it does not require a perfect complex. Thus the maps used here are compatible with both the strict transitions and their canonical derived coefficient identifications.

Cited statements: lem-pc-kflat-resolution, lem-pur-kflat-change-of-rings, lem-weil-pbc-proetale-derived-pullback-composition, lem-trf-scheme-galois-coefficient-change, lem-trf-point-sections-finite-reduction, def-weil-derived-complete-integral-detailed.

**Old Step 6.** For $N=P_{\mathcal O_E}K$, [lem-trf-integral-point-transport-tower-realization] identifies each specified integral $\iota_{H_{\mathcal O_E}^jN}$ with realization of the actual point-transport morphism of its coherent quotient tower. The formulas for $c$ and $\eta$ in [lem-trf-integral-pullback-comparison-realization] identify the integral composition map itself with realization of the strict termwise composition maps, including the comparison from the realized iterated tower to the iterated completed pullback. Apply those formulas to the square $g^m\bar y=\bar y h$ and to each splitting into successive pullbacks. The strict left-hand map of Step 5 is the composite of these termwise composition maps and the finite point transports. Its realization is therefore exactly $\operatorname{Fib}_s(v_{\mathcal O_E,K})I^{(m)}_{P_{\mathcal O_E}K}$ of Step 2. The right-hand map realizes, by the same specified composition identifications, to the stipulated realization of $J_y(\kappa^{(m)})\rho$. Apply the functor $R\lim$ of [lem-weil-pbc-ringed-strict-tower-homotopy-limit] to the equality of whole strict maps from Step 5. This proves the integral equality. No step infers an integral equality solely from equal individual reductions, and no finite Tor-amplitude assumption enters.

Cited statements: lem-trf-integral-point-transport-tower-realization, lem-trf-integral-pullback-comparison-realization, lem-weil-pbc-ringed-strict-tower-homotopy-limit.

**Old Step 7.** By [def-weil-rationalization-karoubi] the objects at $E$ are the integral objects and their morphisms are $\operatorname{Hom}_{\mathcal O_E}\otimes E$. By [def-weil-frobenius-point-transport] the rational point transport is the scalar extension of the integral transport. Applying rationalization to Step 6 gives the required normalization at $E$. For rational naturality it suffices to take a morphism $f\otimes\lambda$: both sides of the naturality equation of Step 2 become $\lambda$ times the rationalization of its integral equation for $f$, by the linear formulas for pullback in [def-weil-derived-pullback-tensor-hom] and for the point functor in [def-weil-finite-coefficient-point]. Additivity gives the equation for every morphism. Thus this argument covers morphisms in the raw framework rationalization and does not replace it by a larger category or invoke an idempotent completion.

Cited statements: def-weil-rationalization-karoubi, def-weil-frobenius-point-transport, def-weil-derived-pullback-tensor-hom, def-weil-finite-coefficient-point.

### lem-trf-iterated-return-transport-scalar-calculus

Assigned returned steps: 2, 8, 9.

**Old Step 2.** Let $H_\Lambda=Lg_{s,\Lambda}^*$ and $P_\Lambda=L\bar y_\Lambda^*$. Define $I^{(0)}_N=1$ and $I^{(j+1)}_N=\iota_{H_\Lambda^jN}\,I^{(j)}_N$, so $I^{(m)}_N:\operatorname{Fib}_sN\to\operatorname{Fib}_sH_\Lambda^mN$. Each $\iota$ is the specified map of [def-weil-frobenius-point-transport]. By [lem-weil-frobenius-point-transport-natural](2), induction gives $\operatorname{Fib}_s(H_\Lambda^m v)I^{(m)}_N=I^{(m)}_{N'}\operatorname{Fib}_s(v)$ for every $v:N\to N'$: apply the one-step naturality equation to $H_\Lambda^jv$ and compose with the induction equation. The scheme equality in Step 1 gives a natural comparison $v_{\Lambda,K}:H_\Lambda^mP_\Lambda K\xrightarrow{\sim}P_\Lambda G_\Lambda^mK$ using [lem-weil-pbc-proetale-derived-pullback-composition] at finite level, [lem-pod-integral-pullback-composition] integrally, and their rationalizations. Put $t_{y,m,K}=\operatorname{Fib}_s(v_{\Lambda,K})I^{(m)}_{P_\Lambda K}$. Naturality of $v$ and the displayed induction equation give exactly $J_y(G_\Lambda^mu)t_{y,m,K}=t_{y,m,L}J_y(u)$.

Cited statements: def-weil-frobenius-point-transport, lem-weil-frobenius-point-transport-natural, lem-weil-pbc-proetale-derived-pullback-composition, lem-pod-integral-pullback-composition.

**Old Step 8.** Write $T_s$ for scalar extension on $s$, $a_K:T_sP_EK\to P_MTK$ for the pullback comparison, and $\delta_N:T_sH_E^mN\to H_M^mT_sN$ for the iterated point pullback comparison. The comparisons are now specified by [lem-trf-integral-pullback-comparison-realization], not characterized by their individual reductions. Its composition/scalar equation, applied along the two equal scheme maps $g^m\bar y=\bar y g_s^m$, and then along every splitting of $g^m$ and $g_s^m$, gives
$$v_{M,TK}H_M^m(a_K)\delta_{P_EK}=P_M(d_K)a_{G_E^mK}T_s(v_{E,K}).$$
Indeed its left path first uses the scalar comparisons for the successive point pullbacks and for $\bar y$, and then the compositor defining $v_M$; its right path first uses $v_E$, then the scalar comparison for $\bar y$ and the successive $g$ pullbacks. The lemma's equation interchanges a scalar comparison with each compositor, and its equality-of-scheme-maps and associativity clauses identify the two paths. These are equalities of the specified simultaneous quotient-diagram maps and hence their integral realizations; the rationalization clause gives the displayed equation. The identity and coefficient-tower clauses use the completion-normalized tensor associator, matching that in [lem-weil-point-sections-scalar-extension]. No assertion about the unaccepted proof of lem-pur-integral-operations-scalar-extension is used.

Cited statements: lem-trf-integral-pullback-comparison-realization, lem-weil-point-sections-scalar-extension.

**Old Step 9.** Let $\beta_N:\operatorname{Fib}_{s,E}N\otimes_E M\to\operatorname{Fib}_{s,M}T_sN$ be the inverse of the rational sections comparison of [lem-weil-point-sections-scalar-extension]. The scalar-compatibility clause of [lem-weil-frobenius-point-transport-natural](2) gives, for one step, $\operatorname{Fib}_{s,M}(\delta_N)\beta_{H_EN}(\iota_N\otimes M)=\iota_{T_sN}\beta_N$. Apply that equation in turn to $N,H_EN,\ldots,H_E^{m-1}N$; naturality of $\iota$ moves each intermediate pullback comparison across the next transport. The adjacent comparison factors compose to the iterated $\delta_N$, giving
$$\operatorname{Fib}_{s,M}(\delta_N)\beta_{H_E^mN}(I_N^{(m)}\otimes M)=I_{T_sN}^{(m)}\beta_N.$$
The point comparisons are exactly those of Step 8: the strict-system choices and their scalar associator are specified by [lem-trf-integral-pullback-comparison-realization]. For identity and successive field extensions the equations use the identity and associator clauses of [lem-weil-point-sections-scalar-extension] and [lem-pur-integral-operations-scalar-extension], so the same induction gives those compatibilities for every $m$.

Cited statements: lem-weil-point-sections-scalar-extension, lem-weil-frobenius-point-transport-natural, lem-pur-integral-operations-scalar-extension, lem-trf-integral-pullback-comparison-realization.

### Parent assembly

**Old Step 10.** By its definition in the statement, $b_K=\operatorname{Fib}_{s,M}(a_K)\beta_{P_EK}$. Expand $t_{y,m,K}=\operatorname{Fib}_{s,E}(v_{E,K})I^{(m)}_{P_EK}$ on the left-hand side of the desired coefficient equation. Naturality of $\beta$ with respect to $v_{E,K}$ rewrites it as
$$\operatorname{Fib}_{s,M}\!\left(P_M(d_K)a_{G_E^mK}T_s(v_{E,K})\right)\beta_{H_E^mP_EK}(I^{(m)}_{P_EK}\otimes M).$$
Substitute the square proved in Step 8 and the iterated point equation of Step 9. The result is
$$\operatorname{Fib}_{s,M}\!\left(v_{M,TK}H_M^m(a_K)\right)I^{(m)}_{T_sP_EK}\beta_{P_EK}.$$
Naturality of $I^{(m)}$ for $a_K$, proved in Step 2, makes this $\operatorname{Fib}_{s,M}(v_{M,TK})I^{(m)}_{P_MTK}\operatorname{Fib}_{s,M}(a_K)\beta_{P_EK}=t_{y,m,TK}b_K$. This proves the final displayed equation. The identity and tower identifications remain the specified ones because each substitution uses the same comparisons as Steps 8 and 9. The naturality of $\beta$ used here is part of [lem-weil-point-sections-scalar-extension].

## Not duplicates

lem-trf-finite-return-frobenius-cancellation vs lem-trf-frobenius-stalk-trivialization-normalization: that statement computes represented germs of geometric stalks; the new task computes final-object point sections and cancels the specified scheme/Galois comparison around a return square, including its chain-map normalization.

lem-trf-finite-return-frobenius-cancellation vs lem-trf-fixed-point-stalk-transport-cocycle: that node defines transport using kappa and proves its cocycle; it does not identify it with successive restriction-defined point transports.

lem-trf-finite-return-frobenius-cancellation vs prop-trf-scheme-galois-comparison: the existing statement gives the comparison functor isomorphism, not its normalization after fixed-point pullback against point restriction.

lem-trf-finite-return-frobenius-cancellation vs lem-pur-frobenius-trivialization-pullback: the existing statement gives the pullback-compatible trivialization; the new statement identifies its final-object value and the finite return-square cancellation.

lem-trf-finite-return-frobenius-cancellation vs lem-trf-absolute-frobenius-site: the shared Stacks tag supplies relative-Frobenius input; this existing node does not assert the combined final-object restriction formula and finite fixed-point return-square chain identity required by the new task.

lem-trf-finite-return-frobenius-cancellation vs lem-zl-general-condensed-weil-realization: the shared Stacks tag supplies relative-Frobenius input; this existing node does not assert the combined final-object restriction formula and finite fixed-point return-square chain identity required by the new task.

lem-trf-finite-return-frobenius-cancellation vs lem-zl-constant-weil-datum: the shared Stacks tag supplies relative-Frobenius input; this existing node does not assert the combined final-object restriction formula and finite fixed-point return-square chain identity required by the new task.

lem-trf-finite-return-frobenius-cancellation vs prop-trf-graph-frobenius-operator: the shared Stacks tag supplies relative-Frobenius input; this existing node does not assert the combined final-object restriction formula and finite fixed-point return-square chain identity required by the new task.

lem-trf-finite-return-frobenius-cancellation vs lem-trf-scheme-galois-coefficient-change: the shared Stacks tag supplies relative-Frobenius input; this existing node does not assert the combined final-object restriction formula and finite fixed-point return-square chain identity required by the new task.

lem-trf-finite-return-frobenius-cancellation vs lem-trf-local-frobenius-transport-normalization: the shared Stacks tag supplies relative-Frobenius input; this existing node does not assert the combined final-object restriction formula and finite fixed-point return-square chain identity required by the new task.

lem-trf-finite-return-frobenius-cancellation vs lem-trf-local-frobenius-conjugacy: the shared Stacks tag supplies relative-Frobenius input; this existing node does not assert the combined final-object restriction formula and finite fixed-point return-square chain identity required by the new task.

lem-trf-finite-return-frobenius-cancellation vs lem-trf-absolute-frobenius-coefficient-naturality: the shared Stacks tag supplies relative-Frobenius input; this existing node does not assert the combined final-object restriction formula and finite fixed-point return-square chain identity required by the new task.

lem-trf-finite-return-frobenius-cancellation vs lem-trf-graph-frobenius-unit-comparison: the shared Stacks tag supplies relative-Frobenius input; this existing node does not assert the combined final-object restriction formula and finite fixed-point return-square chain identity required by the new task.

lem-trf-finite-return-frobenius-cancellation vs def-weil-pbc-proetale-operations: the shared Stacks tag supplies relative-Frobenius input; this existing node does not assert the combined final-object restriction formula and finite fixed-point return-square chain identity required by the new task.

lem-trf-local-normalization-strict-realization vs lem-trf-integral-point-transport-tower-powers: that node treats point-only inverse-image systems and their power compositors; the new task lifts equality of local fixed-point/scheme-Galois comparison recipes on a scheme to the completed local return square, including derived quotient comparisons and raw rationalization.

lem-trf-local-normalization-strict-realization vs lem-trf-integral-point-transport-tower-realization: that node realizes one point transport; the new node identifies both entire local normalization recipes, their transition and derived coefficient compatibility, and their rationalization.

lem-trf-local-normalization-strict-realization vs lem-trf-integral-pullback-comparison-realization: that node constructs composition and scalar families; the new task identifies the realization of the composite local Frobenius normalization maps built using those families.

lem-trf-local-normalization-strict-realization vs lem-trf-fixed-stalk-identification-reduction: that statement assumes finite Tor-amplitude and concerns fixed-point identification under one reduction; the new task concerns simultaneous strict quotient systems and requires no finite Tor-amplitude.

lem-trf-iterated-return-transport-scalar-calculus vs lem-weil-frobenius-point-transport-natural: that node gives one-step naturality and scalar compatibility; the new task proves the iterated point equation together with the return-square compositor/scalar equation for the same comparison families.

lem-trf-iterated-return-transport-scalar-calculus vs lem-trf-frobenius-transports-scalar-extension: that node concerns compact-support cohomology and its exchange; the new task concerns a local point pullback and the two intermediate iterated equations, without compactification.

lem-trf-iterated-return-transport-scalar-calculus vs lem-trf-integral-pullback-comparison-realization: that node supplies generic composition/scalar coherence; the new task combines its return-square specialization with the induction on specified point transports. No single one-line specialization supplies both equations.

## Search review

The exact executed queries, hit summaries and verdicts are recorded in each new node and `searches.jsonl`. Two semantic phrasings were used per task. Finite-field Frobenius ring identities, Zariski module pullback composition, ordinary inverse systems, adic completion of modules and generic naturality do not assert these specified derived pro-etale comparisons. No result was marked as a Mathlib match on the basis of its name. No search was fabricated.
