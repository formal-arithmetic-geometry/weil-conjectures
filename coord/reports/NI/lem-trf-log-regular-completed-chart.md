# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-log-regular-completed-chart.json`: statement unchanged verbatim; a short six-step assembly replaces the seven-step 7775-character proof.
- `dag/nodes/sec-trace-formula/lem-trf-completed-chart-coefficient-surjection.json`: statement, unsplit, no Mathlib match. Chooses coefficients and prescribed parameter lifts and constructs the completed monoid surjection, including its ideal images and completion invariants.
- `dag/nodes/sec-trace-formula/lem-trf-polynomial-power-series-monoid-completion.json`: statement, unsplit, no Mathlib match. Constructs compatible finite quotient comparisons and the resulting monoid/variable-compatible completed-ring identification.
- `dag/nodes/sec-trace-formula/lem-trf-cohen-monoid-surjection-principal-kernel.json`: statement, unsplit, no Mathlib match. For an arbitrary surjection with full boundary image and the dimension hypothesis, constructs the relation and identifies the principal kernel.
- `citations.json`: a verbatim supporting statement for each cited node of each assembly step. Search command output and its log are retained in `search-results.json` and `searches.jsonl` in the sandbox.

## Attachments

None. Read `lean/Sheaf/AlgebraicGeometry/LogRegularCompletedChart.lean`: `AlgebraicGeometry.exists_completed_chart_of_logRegular` at line 177 ends in `sorry` at line 234. The upstream `lean/WeilConjectures/` searches for the blueprint tag, LogRegular/log_regular, completed-chart names and monoid-completion/kernel terminology did not find a finished declaration stating the whole item or any extracted lemma. No Lean was written or compiled.

## WANTED

WANTED: Kato (1994), Theorem 3.2, for the original completed-chart structure theorem, and Theorem 4.1 for the existing saturated-model normality input. These remain unavailable locally as already recorded by the returned node. The proof still has agent origin: I read ILO Exposé VI 1.2 and 1.6 directly (printed pp. 69--70, PDF pp. 75--76), which states the model formulas and references Kato, and read the local Stacks Cohen structure proof rather than claiming to have read Kato.

## Repair of the return

The only return point is the human's re-split directive. The sandbox initially had just dispatcher markers, not any node/report/search record, so the current read-only repository item (with exactly the returned seven step lengths) was the retained-head baseline. I copied it to the sandbox, preserving its statement, metadata, earlier searches and prior proof as the archive below. I changed no repository or launcher file and ran no git command myself.

Three new unsplit, statement-only nodes divide the old algebra argument; their statements are 1920, 1442 and 1608 characters. They have independent hypotheses and no proof steps. The parent's assembly is below 3000 characters. The first task does not identify its kernel; the second concerns two different presentations of the source and assumes no target ring; the third starts from an already-given surjection and proves the kernel, without choosing coefficients or constructing a log chart. None restates the log-scheme theorem or all its work.

Allocation of every old argument: old Step 1 stays in assembly Step 1, with the pushout/nonunit explanation written explicitly. Old Step 2, including lifting the quotient parameters, generating the maximal ideal, the completion invariants, characteristic-zero and characteristic-p coefficient selection, the finite-level maps and inverse limit, and complete-source surjectivity, is the coefficient-surjection node. Old Step 3's finite-quotient comparison, limit and monomial quotient are the comparison node; its regularity and dimension assertions continue to be obtained from the existing power-series regularity and formal-monoid dimension nodes, in assembly Step 3. Old Step 4's prime-chain proof is still written in assembly Step 4 and is also the final injectivity argument allocated to the kernel task. Old Step 5's lift j, theta=p-j, primitive reduction, domain/dimension quotient and kernel identification are the kernel node. Old Step 6's chart compatibility and old Step 7's empty-monoid/empty-variable cases stay in assembly Step 6 and are included in the new statements where relevant. The complete original text is reproduced below, not lost or replaced by a vague assertion.

One small clarification was needed in the assembly: the parent calls the no-field case characteristic (0,p). Its old argument constructed the model but did not explicitly conclude char(A)=0. After the kernel task gives the domain S, I now cite the existing Mathlib leaves for faithfully flat completion and universal injectivity, applied to N=A, so A injects into S and is a domain. A positive-characteristic domain contains its prime field, contrary to the no-field assumption. This closes the classification without any change to the parent's statement or a new node for an elementary consequence.

## Blueprint and duplicate searches

Read `GOAL.md`, the three blueprint levels in `SETUP.md`, chapter `sec-trace-formula` and unit `sk-i-curve-zero`. The nearest blueprint ancestor is `lem-trf-local-term-locality`. Its current blueprint_update concerns contracting local terms; the present local-chart work is below the recorded alteration/nearby-duality ancestry, not an alternative proof of the unit. Each child retains that ancestor with the item prepended to the via list and names the exact former completed-chart step it serves.

Ran `tools/blueprint_refs.py ancestor lem-trf-log-regular-completed-chart` and whole-blueprint searches for monoid, Cohen, completion, monoid completion, and principal kernel (also an initial combined pattern). The combined-word hits were the general chapter conventions and unrelated Picard/purity nodes, not these commutative-algebra statements. Whole-DAG searches covered source tags 032A/032C/0315/07NV/00KQ and monoid/completion, prescribed coefficient surjection and principal-kernel terminology. I opened the formal-monoid dimension, saturated normality, monoid coefficient-description, formal-monoid extension, formal-monoid evaluation, implicit-elimination, Cohen presentation/parameter-extension, and separable closed-point presentation statements. No existing statement supplies the three tasks. In particular I did not recreate the previously rejected completed-model-dimension conjunction.

## Not duplicates

lem-trf-completed-chart-coefficient-surjection vs lem-trf-relative-cohen-flat-presentation: the latter assumes a flat local Q-algebra map and a regular closed fibre and gives compatible relative power-series presentations; the new lemma constructs a monoid map with prescribed images, including positive residue characteristic, without a flat map hypothesis.
lem-trf-completed-chart-coefficient-surjection vs lem-weil-pbc-power-series-first-order-coordinates: the latter only identifies a square-zero quotient over a field, not a completed monoid surjection.
lem-trf-completed-chart-coefficient-surjection vs lem-weil-pbc-local-first-order-coordinates: the latter assumes an existing coefficient section and identifies A/m^2; the new lemma chooses coefficients and constructs a surjection onto the full completion.
lem-trf-completed-chart-coefficient-surjection vs lem-weil-pbc-complete-local-domain-finite-over-regular: the latter supplies a finite subring in a complete domain; the new lemma assumes no domain property and uses a prescribed monoid and parameter images.
lem-trf-completed-chart-coefficient-surjection vs lem-weil-pbc-first-order-power-series-comparison: the latter maps a complete local algebra to a first-order square-zero ring, in the opposite direction from the full completed chart presentation.
lem-trf-completed-chart-coefficient-surjection vs lem-weil-pbc-power-series-universal-property-complete: the latter starts with coefficients and variable images and extends a power-series map; it neither chooses a coefficient ring nor handles prescribed monoid relations or proves this surjectivity.
lem-trf-completed-chart-coefficient-surjection vs lem-weil-pbc-cohen-power-series-presentation: the existing result gives unspecified power-series variable images; the new result needs every z^q to map to the chosen a(q) and every T_i to the chosen quotient-parameter lift, with full boundary image. The existing result is a coefficient input, not an exact match.
lem-trf-completed-chart-coefficient-surjection vs lem-weil-pbc-cohen-structure-power-series-surjection: unspecified free variables and no monoid or boundary images versus a prescribed monomial chart and parameter lifts.
lem-trf-completed-chart-coefficient-surjection vs lem-weil-pbc-cohen-ring-lift-complete-local: the latter lifts a given Cohen ring and residue isomorphism; the new lemma selects the field/Cohen case and constructs the monoid completion surjection.
lem-trf-completed-chart-coefficient-surjection vs lem-weil-pbc-coefficient-residue-section: the latter supplies only the characteristic-zero section, not the positive-characteristic field/Cohen alternatives or prescribed chart map.
lem-trf-completed-chart-coefficient-surjection vs lem-weil-pbc-coefficient-subring-principal-source: the latter studies the image of an already chosen complete PID map; the new lemma constructs a completed chart presentation and proves its surjectivity.
lem-trf-completed-chart-coefficient-surjection vs lem-weil-pbc-cohen-coefficient-ring-exists: the latter supplies only a coefficient subring, not the prescribed monoid-polynomial surjection and ideal images.
lem-trf-completed-chart-coefficient-surjection vs lem-weil-pbc-power-series-quadratic-ideal: the latter is a criterion for a series to lie in the square of the variable ideal; it says nothing about coefficient choices or monomial evaluation.
lem-trf-completed-chart-coefficient-surjection vs lem-per-formal-monoid-adic-evaluation: the latter assumes a coefficient homomorphism, extends an evaluation and proves congruence continuity, but neither chooses the coefficients nor proves the full surjection with the specified parameter lifts.
lem-trf-polynomial-power-series-monoid-completion vs lem-trf-formal-monoid-ring-dimension: the existing lemma starts from D[P] with D already complete regular local. It does not identify its completion with the completion of L[P][T] or identify each finite quotient. The new lemma constructs that comparison and does not repackage the dimension conclusion.
lem-trf-polynomial-power-series-monoid-completion vs lem-trf-monoid-completion-coefficients: the existing statement describes coefficients of a completion with an already-complete local coefficient ring and a positive grading. It does not compare polynomial and power-series coefficient presentations or their canonical maps.
lem-trf-polynomial-power-series-monoid-completion vs lem-per-formal-monoid-implicit-elimination: the latter eliminates unit-twisted monomial relations in a quotient of D[[S+T]], whereas the new lemma compares completion before and after completing the coefficient variables, with no relation imposed.
lem-trf-cohen-monoid-surjection-principal-kernel vs lem-trf-log-regular-saturation-normality: the existing lemma assumes theta and proves normality of the model. The new lemma starts with phi, constructs theta, and proves the entire kernel equals (theta) using dimension. Normality is its input, not its conclusion alone.
lem-trf-cohen-monoid-surjection-principal-kernel vs lem-trf-formal-monoid-ring-dimension: the existing lemma computes dimension and proves a parameter is regular; it does not construct p-j from the boundary image or rule out further kernel relations of phi.
lem-trf-cohen-monoid-surjection-principal-kernel vs lem-trf-log-regular-completed-chart: the new lemma has no log scheme, geometric point, strict henselization, sharp-chart existence, parameter choice, coefficient-ring existence or equal-characteristic case. It is the independent final algebraic argument for any given phi satisfying its hypotheses.

## Review by NI

I read the item against ILO VI 1.2 and 1.6(i)--(ii): local Noetherian fs log regular scheme, the sharp characteristic chart, completed strict local ring, arbitrary residue field and the two exact monomial models all agree. The condition is theta congruent to p modulo the monomials AND the parameters, not just modulo the monomials. The item's statement, all its hypotheses and its permitted chart replacement remain verbatim. The source does not prove the three extracted algebra tasks in detail; their source places explicitly say they are agent refinements of the old constructive proof. I read Stacks algebra.tex at theorem-cohen-structure-theorem (032A) and remark-Noetherian-complete-local-ring-universally-catenary (032C), plus definition-cohen-ring (0327); coefficients in positive residue characteristic really come from a Cohen ring, including an imperfect residue field. The unavailable Kato text has not been used as if read.

For Step 1, the sharp-chart statement actually supplies the affine locally Noetherian neighbourhood and fs sharp P. The definition node actually states the chart pushout and the log-regular quotient/dimension criterion. Thus the nonunits are units times the a(q), q nonzero, and no extra chart theorem is silently invoked. The strict-henselization Noetherian theorem applies to O_{X,x}, Noetherian by the local-Noetherian hypothesis; its conclusion is about A itself.

For Step 2, I checked the full new coefficient-surjection statement. Its hypotheses are just those obtained in Step 1, and its conclusions explicitly include existence of parameter lifts, compatible coefficient maps, the images of all monomials and variables, surjectivity, full boundary ideal image, and completion dimension. The complete-source surjectivity argument from old Step 2 has not been marked elementary or hidden in the parent: it is the work assigned to that child. The child does not assume A already has the desired presentation, and regularity is assumed only for A/I.

For Step 3, the new comparison statement actually identifies E/a^j with D[P]/b^j by the natural inclusion at every j and says these maps commute with transition maps. This is stronger and more precise than a vague identification of the completed rings. The power-series regularity statement then provides the complete regular local domain D and its exact dimensions n and n+1. The formal-monoid dimension theorem is applied with that D and T=P and explicitly supplies a Noetherian local integral domain of dimension dim(D)+r. No source regularity or dimension hypothesis is omitted, and no property of a node's proof rather than its statement is used.

For Step 4, the equal-characteristic map and the two dimensions were established already. The zero prime is prime because its source is a domain; finite Krull dimension is attained by a chain. A nonzero kernel forces each preimage prime in the quotient chain to be nonzero, so adjoining (0) contradicts the dimension. This is the same elementary prime-chain argument as old Step 4, now marked elementary with the dimension definition cited. I did not create a lemma for this few-line consequence.

For Step 5, the new kernel statement assumes precisely surjectivity, locality, phi(J)=m_S, nonzero Noetherian local S and dim(S)=n+r, all supplied by Step 2. It explicitly gives j, theta-p in J, the primitive reduction in C[[T]], the domain quotient and the kernel equality. Its work package contains the old normality/dimension/injectivity argument, not merely the easy construction of j. For the source's (0,p) terminology I also opened both completion faithful-flatness and faithful-flat universal-injectivity statements: taking N=A and A tensor_A S=S gives an injection. The domain conclusion of the kernel task then makes A a domain; a nonzero prime characteristic would supply a field inside A, so it has characteristic zero. These two generic tools are existing Mathlib leaves and introduce no new unfinished branch.

For Step 6, all monomial equalities were explicit outputs of Step 2 and preserved by the kernel task. Inversion supplies the isomorphism direction in the item; W'=W retains its characteristic identification from Step 1. If P is trivial, I=0. If n=0, the maximal ideal is I. If both hold A is already a field, so the no-field case is never needed there. There is no change of chart or hidden descent assertion.

Small cases checked for each child: (a) the coefficient task for a field with P=0,n=0 is the identity; for F_p[x]_(x) with P=N and a(1)=x it gives F_p[[z]] onto F_p[[x]]; with P=0 and A=Z_p it gives Z_p[[T]] onto Z_p by T mapping to p, so the Cohen uniformizer need not be an independent parameter in the target; its general no-field case also permits Z/p^2 without wrongly asserting that arbitrary A is characteristic zero. (b) the comparison with n=0 is the identity completion of L[P]; with P=0 it is the usual finite truncation of L[T] and L[[T]], including p-adic coefficient powers for a Cohen ring; for P=N and two variables, truncation retains exactly the total-degree terms below j. (c) the kernel task for C=Z_p,P=0,n=0,S=F_p gives J=0,theta=p; for P=N,n=0,S=Z_p and z mapping to p it gives theta=p-z; with P=N^2,n=0,S=Z_p[[x,y]]/(xy-p), j=xy and theta=p-xy, the quotient has dimension 2 as required. Removing the dimension hypothesis would allow extra relations and is deliberately not done. All three tasks include the empty-variable and trivial-monoid cases, all rings and maps are introduced in the statements, and no perfection, smoothness or excellence hypothesis has been slipped in.

I checked delivery-errors B--E against these files: statement-only children have no proof; source places distinguish actual source formulas from agent refinements; TeX has single logical backslashes after JSON decoding; notions cite actual definition nodes; existing Mathlib results remain leaves rather than new tasks. The duplicate comparisons above distinguish all same-032A source hits and the close monoid statements I opened. The query texts and raw results in every new node are exactly from msearch.py, including the unavailable LeanSearch requests. Loogle and LeanFinder ran; a second semantic phrasing was run for every task and the parent. I read the general completion-surjectivity and Laurent-series hits: none constructs the requested coefficient/monoid map, none compares these two monoid-coefficient completions, and the kernel/cotangent hits do not give the principal-kernel theorem here. None of the three children depends on its parent or on a descendant of the item; their proofs remain open tasks as required. No step exceeds 2000 characters and the assembly is below 3000. The new tasks are comparable in size; I retained all old arguments in the archive rather than discarding the details to meet a count.

## Validation

Before this report was written, the required server `srvcheck.py ... review_split` returned PASS. The required `deliver.py NI lem-trf-log-regular-completed-chart --no-push` exited 0 with `OK (not pushed)` at dry-run commit `2d88f96bae7`; server preflight passed. The final push also runs preflight on the packaged delivery.

## Previous seven-step argument retained verbatim

### Former Step 1

Let $a:P\to A$ be the sharp chart of [lem-trf-log-regular-sharp-chart], defined on an affine locally Noetherian pointed etale neighbourhood $(W,\bar w)$ of $\bar x$ [def-weil-pbc-pointed-etale-neighbourhoods] and inducing the chosen identification $P\cong\overline M_{\bar x}$; that lemma also gives that $P$ is finitely generated, integral, saturated and sharp. We take $W'=W$ and keep this chart: the replacement allowed in the statement is not needed. By the definition of a chart [def-trf-fs-log-blowup], $M_{\bar x}=P\oplus_{a^{-1}(A^\times)}A^\times$, and since $P\to\overline M_{\bar x}$ is bijective and $P$ is sharp, $a(q)$ is a nonunit exactly when $q\neq0$; hence the ideal $I$ generated by the images of the nonunits of $M_{\bar x}$ is $I=(a(q):q\neq0)A$, generated by the images of finitely many generators of $P$. Log regularity at $\bar x$ [def-trf-fs-log-blowup] says that $R=A/I$ is a regular local ring and $\dim A=\dim R+r$, with $r=\operatorname{rank}_{\mathbf Z}P^{\rm gp}$. The local ring $\mathcal O_{X,x}$ is Noetherian because $X$ is locally Noetherian, so its strict henselization $A$ is Noetherian [lem-sc-strict-henselization-noetherian].

Used statements: lem-trf-log-regular-sharp-chart, def-weil-pbc-pointed-etale-neighbourhoods, def-trf-fs-log-blowup, lem-sc-strict-henselization-noetherian.

### Former Step 2

Put $n=\dim R$ and choose a regular system of parameters $\bar t_1,\ldots,\bar t_n$ of $R$, with lifts $t_1,\ldots,t_n\in A$. Since $\mathfrak m_R=(\bar t_1,\ldots,\bar t_n)$, the maximal ideal of $A$ is $\mathfrak m_A=I+(t_1,\ldots,t_n)=(a(q)\ (q\neq0),t_1,\ldots,t_n)A$. The completion $\widehat A$ is Noetherian [lem-weil-pbc-adic-completion-noetherian], local with maximal ideal $\mathfrak m_A\widehat A$ and residue field $k$ [lem-weil-pbc-local-completion-local-ring], complete for $\mathfrak m_A\widehat A$ [lem-weil-pbc-adic-completion-mod-ideal](1), and $\dim\widehat A=\dim A=n+r$ [lem-weil-pbc-completion-dimension]. Apply the Cohen presentation [lem-weil-pbc-cohen-power-series-presentation] to $\widehat A$ and restrict its surjection to the coefficient ring: this gives a ring map $\lambda:\Lambda\to\widehat A$ with $\Lambda$ a field mapping isomorphically to $k$ when $\operatorname{char}k=0$, and a Cohen ring $\Lambda$ with $\Lambda/p\Lambda\cong k$ when $\operatorname{char}k=p>0$. If $A$ contains a field, then either $\operatorname{char}k=0$ and we put $L=\Lambda$, or $\operatorname{char}k=p>0$, the field has characteristic $p$, $p=0$ in $\widehat A$, and $\lambda$ factors through $\Lambda/p\Lambda\cong k$; in both cases $L=k$ is a coefficient field of $\widehat A$. If $A$ contains no field, then $\operatorname{char}k=p>0$ (otherwise every nonzero integer is a unit of the local ring $A$ and $\mathbf Q\subset A$), and we put $L=C=\Lambda$. Define $\phi_0:L[P][t_1,\ldots,t_n]\to\widehat A$ by $cz^qt^e\mapsto\lambda(c)a(q)t^e$; it is a ring map because $a$ is a monoid map to $(A,\cdot)$, and it sends the finitely generated ideal $\mathfrak a=(\mathfrak m_L,z^q\ (q\neq0),t_1,\ldots,t_n)$ into $\mathfrak m_A\widehat A$ (in the Cohen case $\lambda(p)=p\in\mathfrak m_A$ since $\operatorname{char}k=p$). As $\widehat A$ is complete, $\phi_0$ induces compatible maps $L[P][t_1,\ldots,t_n]/\mathfrak a^j\to\widehat A/\mathfrak m_A^j\widehat A$ and hence a continuous local map $\phi:B_L(P,n)\to\widehat A$ [def-weil-pbc-adic-completion] with $\phi(z^q)=a(q)$ and $\phi(t_i)=t_i$. Surjectivity: $B_L(P,n)$ is complete for $\mathfrak n=\mathfrak aB_L(P,n)$ [lem-weil-pbc-adic-completion-mod-ideal](1); $\mathfrak n\widehat A$ is generated by $p$ (Cohen case), the $a(q)$ and the $t_i$, so it equals $\mathfrak m_A\widehat A$, for which $\widehat A$ is Hausdorff; and $B_L(P,n)\to\widehat A/\mathfrak m_A\widehat A=k$ is onto because $\Lambda\to k$ is. Hence $\phi$ is surjective [lem-weil-pbc-complete-source-surjective-mod-ideal].

Used statements: lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-local-completion-local-ring, lem-weil-pbc-adic-completion-mod-ideal, lem-weil-pbc-completion-dimension, lem-weil-pbc-cohen-power-series-presentation, def-weil-pbc-cohen-ring, def-weil-pbc-adic-completion, lem-weil-pbc-complete-source-surjective-mod-ideal.

### Former Step 3

Put $D=L[[t_1,\ldots,t_n]]$ [def-weil-pbc-multivariate-power-series]. It is a complete regular Noetherian local ring with maximal ideal $\mathfrak m_D=(\mathfrak m_L,t_1,\ldots,t_n)$ and $\dim D=n$ if $L=k$, $\dim D=n+1$ if $L=C$; in the Cohen case $p,t_1,\ldots,t_n$ is a regular system of parameters, since these $n+1=\dim D$ elements generate $\mathfrak m_D$ [lem-weil-pbc-power-series-field-cohen-regular-complete]. For every $j$ the inclusion $L[P][t_1,\ldots,t_n]\subset D[P]$ induces an isomorphism $L[P][t_1,\ldots,t_n]/\mathfrak a^j\cong D[P]/\mathfrak a_D^j$, $\mathfrak a_D=(\mathfrak m_D,z^q\ (q\neq0))$, because $\mathfrak a^j$ contains every monomial $t^e$ with $|e|\ge j$ and $D/\mathfrak m_D^j=L[t_1,\ldots,t_n]/(\mathfrak m_L,t_1,\ldots,t_n)^j$; passing to the limit, $B_L(P,n)$ is the ring $H$ of [lem-trf-formal-monoid-ring-dimension] for $(D,T=P)$, with $N_H=(z^q:q\neq0)H$ and $H/N_H\cong D$. That lemma gives: $B_L(P,n)$ is a Noetherian local integral domain of dimension $\dim D+r$, i.e. $n+r$ for $L=k$ and $n+r+1$ for $L=C$; and for $\eta$ with $\overline\eta\in\mathfrak m_D\setminus\mathfrak m_D^2$, $\eta$ is a nonzerodivisor and $\dim B_L(P,n)/(\eta)=\dim D+r-1$.

Used statements: def-weil-pbc-multivariate-power-series, lem-weil-pbc-power-series-field-cohen-regular-complete, lem-trf-formal-monoid-ring-dimension.

### Former Step 4

Equal characteristic ($A$ contains a field, $L=k$). By Steps 2 and 3, $\phi:B_k(P,n)\to\widehat A$ is a surjection from a Noetherian local domain of dimension $n+r$ onto a ring of dimension $n+r$ [def-weil-pbc-krull-dimension-ring]. If $K=\ker\phi\neq0$, every prime of $B_k(P,n)$ containing $K$ is nonzero, so every chain of primes of $\widehat A\cong B_k(P,n)/K$ gives a chain of primes of $B_k(P,n)$ that can be lengthened by $(0)$, and $\dim B_k(P,n)\ge\dim\widehat A+1$, a contradiction. Hence $\phi$ is an isomorphism $B_k(P,n)\cong\widehat A$ with $z^q\mapsto a(q)$.

Used statements: lem-trf-formal-monoid-ring-dimension, lem-weil-pbc-completion-dimension, def-weil-pbc-krull-dimension-ring, def-trf-fs-log-blowup.

### Former Step 5

Mixed characteristic ($A$ contains no field, $L=C$, $\operatorname{char}k=p$). Let $J=(z^q\ (q\neq0),t_1,\ldots,t_n)B_C(P,n)$. Since $\phi$ is surjective, $\phi(J)$ is the ideal of $\widehat A$ generated by the $a(q)$ and the $t_i$, which is $\mathfrak m_A\widehat A$ by Step 2; as $p\in\mathfrak m_A\widehat A$, choose $j\in J$ with $\phi(j)=p$ and put $\theta=p-j$. Then $\theta\in\ker\phi$ and $\theta-p\in J$. Modulo $N_H=(z^q:q\neq0)$, $\overline\theta\in D=C[[t_1,\ldots,t_n]]$ is congruent to $p$ modulo $(t_1,\ldots,t_n)$; as $p,t_1,\ldots,t_n$ is a regular system of parameters of $D$ (Step 3), $\overline\theta\in\mathfrak m_D\setminus\mathfrak m_D^2$. By [lem-trf-formal-monoid-ring-dimension], $\dim B_C(P,n)/(\theta)=(n+1)+r-1=n+r$, and by [lem-trf-log-regular-saturation-normality](ii), applicable since $\theta-p\in J$, $B_C(P,n)/(\theta)$ is a (normal) integral domain; it is Noetherian local as a quotient of $B_C(P,n)$. Thus $\phi$ induces a surjection $B_C(P,n)/(\theta)\to\widehat A$ from a Noetherian local domain of dimension $n+r$ onto a ring of dimension $n+r$ (Step 2), and the argument of Step 4 shows that it is injective. Hence $\ker\phi=(\theta)$ and $\widehat A\cong B_C(P,n)/(\theta)$, compatibly with $z^q\mapsto a(q)$, where $C$ is a Cohen ring with residue field $k$ [def-weil-pbc-cohen-ring] and $\theta-p\in J$.

Used statements: lem-trf-formal-monoid-ring-dimension, lem-trf-log-regular-saturation-normality, lem-weil-pbc-completion-dimension, def-weil-pbc-cohen-ring, def-weil-pbc-krull-dimension-ring.

### Former Step 6

Compatibility with the chart is built into the construction: $\phi(z^q)=a(q)$ for every $q\in P$, where $a$ is the structural map of the chart $P\to M|_W$ on the affine pointed etale neighbourhood $W'=W$ of Step 1 [lem-trf-log-regular-sharp-chart, def-weil-pbc-pointed-etale-neighbourhoods], which induces the chosen identification of $P$ with $\overline M_{\bar x}$. So the isomorphisms of Steps 4 and 5 are the asserted ones, with the (trivial) chart replacement allowed by the statement.

Used statements: lem-trf-log-regular-sharp-chart, def-weil-pbc-pointed-etale-neighbourhoods.

### Former Step 7

Boundary cases. For $P=\{0\}$ there are no monomials $z^q$ with $q\ne0$, $I=0$ and $A=R$ is regular; for $n=0$ there are no $t_i$ and $\mathfrak m_A=I$. The construction of Steps 2--5 goes through unchanged, with $\mathfrak m_k=0$ and $\mathfrak m_C=pC$ in the completion [def-weil-pbc-adic-completion, def-weil-pbc-cohen-ring]. Both happen together only when $A$ is a field, hence in the equal-characteristic case, where $\widehat A=A=k=B_k(\{0\},0)$.

Used statements: def-weil-pbc-adic-completion, def-weil-pbc-cohen-ring.

## Search record

### lem-trf-cohen-monoid-surjection-principal-kernel

- leanfinder: `A surjection from a completed saturated sharp monoid algebra over a Cohen ring onto a local ring of dimension rank plus parameters has principal kernel theta congruent to p modulo monomials and variables when those generators map onto the maximal ideal.` — no match.
- leansearch: `Principal kernel of a dimension preserving surjection from a mixed characteristic formal toric hypersurface, obtained by lifting p into the monomial and parameter ideal.` — no match.
- loogle: `AdicCompletion, RingHom.ker, Ideal.span` — no match.
- grep: `(Cohen|MonoidAlgebra).*(ker|hypersurface)|(principal|span_singleton).*ker` — no match.
- leanfinder: `In a Cohen formal monoid ring choose j in the boundary ideal mapping to p; dimension and normality of the quotient imply kernel generated by p minus j.` — no match.

Full returned hits are in this node’s `mathlib_searches.results`; raw process outputs are retained in the sandbox.

### lem-trf-completed-chart-coefficient-surjection

- leanfinder: `A Noetherian local ring whose maximal ideal is generated by a sharp monoid chart and parameters admits a surjection from the completed monoid polynomial algebra over a coefficient field or Cohen ring.` — no match.
- leansearch: `Construct a surjective completed monoid algebra map to a complete local ring using a Cohen coefficient ring and prescribed generators of the maximal ideal.` — unavailable.
- loogle: `AdicCompletion, MonoidAlgebra, Function.Surjective` — no match.
- grep: `Cohen.*(Monoid|surject)|Monoid.*(coefficient|surject)|coefficient.*AdicCompletion` — no match.
- leanfinder: `Cohen structure theorem with chosen monomial generators and residue parameters gives a continuous surjective formal toric algebra homomorphism.` — no match.

Full returned hits are in this node’s `mathlib_searches.results`; raw process outputs are retained in the sandbox.

### lem-trf-polynomial-power-series-monoid-completion

- leanfinder: `Completing L[P][t] at the coefficient maximal ideal monomials and variables equals completing L[[t]][P] at the coefficient maximal ideal and monomials, compatibly at each finite quotient.` — no match.
- leansearch: `Truncated polynomial and power series rings with monoid algebra coefficients have identical quotients by powers of the maximal monomial ideal and hence isomorphic adic completions.` — unavailable.
- loogle: `AdicCompletion, MvPowerSeries, MonoidAlgebra` — no match.
- grep: `(MonoidAlgebra|AddMonoidAlgebra).*(MvPowerSeries|AdicCompletion)|(MvPowerSeries|AdicCompletion).*(MonoidAlgebra|AddMonoidAlgebra)` — no match.
- leanfinder: `Adic completion commutes with replacing polynomial coefficients by formal power series in finitely many variables for a finitely generated positive monoid algebra.` — no match.

Full returned hits are in this node’s `mathlib_searches.results`; raw process outputs are retained in the sandbox.

