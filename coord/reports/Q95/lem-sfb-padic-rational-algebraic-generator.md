# Worker report

1. Files written: the item `lem-sfb-padic-rational-algebraic-generator` (statement unchanged; three-step assembly), and two new statement-only nodes in `dag/nodes/sec-six-functors-basics/`:
   - `lem-sfb-padic-minpoly-normed-separation`: statement, status unsplit, no full Mathlib match.
   - `lem-sfb-dense-subfield-algebraic-root-approximation`: statement, status unsplit, no full Mathlib match.
   `citations.json` copies the statement of every cited node verbatim. `searches.jsonl` is the search command's unmodified log; all historical searches on the item are retained.
2. Attachments: none. I searched the project by the blueprint id and concepts and read Extension.lean:76–127. `PadicAlgCl.exists_isAlgebraic_mem_adjoin_simple` is the fixed-model theorem, not the arbitrary-algebraic-closure statement. The exact arbitrary-closure theorem in Sheaf/NumberTheory/Padics/RationalAlgebraicGenerator.lean still has `sorry`.
3. WANTED: none. All sources used below are present.
4. The return asks for a genuine redistribution of the 3229-character proof. No mathematical error or statement dispute was found. The sandbox contained only .brief markers and no retained node/report/search files, so the current live returned node supplied the repair base. All imported/provenance/Lean/review fields were retained. No repository file, Lean file, launcher script or unit/chapter record was changed.
5. The two new nodes remain intentionally unsplit for parallel future workers. No other part is unfinished.

## Return repaired: work allocation

The only numbered issue is the overlarge one-node proof and the demand for at least two comparable new unsplit nodes. New node `lem-sfb-padic-minpoly-normed-separation` carries old steps 1, 2, 3 (1505 characters of argument): extending norm, rational density and the p-adic base hypotheses, separable minimal polynomial, splitting/distinct roots, and the finite conjugate gap including the empty case. New node `lem-sfb-dense-subfield-algebraic-root-approximation` carries old steps 4, 5, 6 (1391 characters): explicit epsilon, dense coefficient approximation with preserved degree, linear-factor splitting, the quantitative nearby-root estimate with equality to the radius, and the evaluation/algebraicity argument. Old step 7 remains the final assembly using existing Krasner. Neither new node asserts field membership or the whole parent conclusion. Both have independent self-contained hypotheses and no proof steps/proof dependencies. The original proof is retained verbatim below so none of the argument is shortened away; these are work instructions for the workers who split the two new nodes, not extra proof steps in their statements.

## Preserved original argument and future proof obligations

### Old step 1 → lem-sfb-padic-minpoly-normed-separation

Put $k=\mathbf Q_\ell$. By [def-weil-l-adic-numbers], $k$ is complete, nonarchimedean and characteristic zero; its norm is nontrivial because $|\ell|_\ell=\ell^{-1}\ne1$. The same definition makes $k$ the completion of $\mathbf Q$, so $\mathbf Q$ is dense in $k$: a Cauchy sequence representing any $a\in k$ has rational terms arbitrarily close to $a$. The given $\Omega/k$ is algebraic by [def-weil-algebraic-closure]. Apply [lem-trf-spectral-norm-algebraic-extension] with $F=k$, $L=\Omega$ to equip this field with a multiplicative nonarchimedean norm extending that of $k$.

Cited nodes: def-weil-l-adic-numbers, def-weil-algebraic-closure, lem-trf-spectral-norm-algebraic-extension.

### Old step 2 → lem-sfb-padic-minpoly-normed-separation

Fix $x\in\Omega$. It is algebraic over $k$ by [def-weil-algebraic-closure]. Take its monic irreducible minimal polynomial $f\in k[T]$ with $f(x)=0$, as in [def-weil-pbc-separable-algebraic-extension]. Its degree $n$ is positive, since a monic constant would be $1$ and could not vanish. Since $k$ has characteristic zero, the leading coefficient of $f'$ is $n\ne0$, so $f'\ne0$. Hence [lem-trf-irreducible-separable-derivative] gives that $f$ is separable. By [lem-pc-separable-polynomial-distinct-roots-alg-closed], $f$ has exactly $n$ distinct roots in $\Omega$ and splits there.

Cited nodes: def-weil-algebraic-closure, def-weil-pbc-separable-algebraic-extension, lem-trf-irreducible-separable-derivative, lem-pc-separable-polynomial-distinct-roots-alg-closed.

### Old step 3 → lem-sfb-padic-minpoly-normed-separation

Let $S$ be the roots of $f$ in $\Omega$ other than $x$. It is finite by step 2. If $S=\varnothing$, set $\delta=1$; otherwise let $\delta$ be the minimum of the finite nonempty set $\{\|x-y\|:y\in S\}$. Each value is positive, so $\delta>0$, and $\delta\leq\|x-y\|$ for every $y\in S$. This includes $n=1$ without taking a minimum of an empty set.

Cited nodes: .

### Old step 4 → lem-sfb-dense-subfield-algebraic-root-approximation

Set $M=\max\{\|x\|,1\}$ and $\varepsilon=(\delta/M)^n/(n+1)>0$. Apply [lem-sfb-monic-dense-approximation] to $\mathbf Q\subseteq k$, $f$ and this $\varepsilon$. It supplies a monic $g\in\mathbf Q[T]$ of degree $n$ whose image $h\in k[T]$ satisfies $\|h_i-f_i\|<\varepsilon$ for every $i$. Field inclusions preserve its leading coefficient $1$ and its zero coefficients above degree $n$, so $h$ is also monic of degree $n$.

Cited nodes: lem-sfb-monic-dense-approximation.

### Old step 5 → lem-sfb-dense-subfield-algebraic-root-approximation

The image of $h$ in $\Omega[T]$ splits by induction on its degree: degree zero is the monic polynomial $1$, an empty product; in positive degree [def-weil-algebraic-closure] gives a root $a$, and division by $T-a$ has remainder $h(a)=0$, leaving a monic quotient of degree one less. Thus induction factors it completely. Apply [lem-sfb-roots-coefficient-proximity] over $k\subseteq\Omega$ to $f,h,x,\varepsilon$. The norm extension is step 1, and the root, monicity, common positive degree and coefficient bound are steps 2 and 4. We obtain $b\in\Omega$ with $h(b)=0$ and
$$\|x-b\|<((n+1)\varepsilon)^{1/n}M=((\delta/M)^n)^{1/n}M=\delta,$$
since $M\geq1$, $\delta>0$ and $n\geq1$.

Cited nodes: def-weil-algebraic-closure, lem-sfb-roots-coefficient-proximity.

### Old step 6 → lem-sfb-dense-subfield-algebraic-root-approximation

For this $b$, $g(b)=h(b)=0$: writing $g=\sum_i q_iT^i$, both evaluations are $\sum_i q_i b^i$ in $\Omega$, because $\mathbf Q\to k\to\Omega$ is the prime-field inclusion. The polynomial $g$ is nonzero since it is monic, so $b$ is algebraic over $\mathbf Q$ by [def-weil-algebraic-element].

Cited nodes: def-weil-algebraic-element.

### Old step 7 → parent assembly

Apply [lem-sfb-complete-normed-krasner] with $K=k$, $L=\Omega$ and $x,b$. Steps 1–2 give its base, extension, separability and splitting hypotheses. For every root $y\ne x$, steps 3 and 5 give $\|x-b\|<\delta\leq\|x-y\|$. The lemma yields $x\in k(b)$. Together with step 6 this proves the statement for the originally given $\Omega$.

Cited nodes: lem-sfb-complete-normed-krasner.

## Sources read and Mathlib searches

I read Stanford L19 Proposition 1.1.9 first bullet, p.3: it invokes countability of finite p-adic extensions in the Baire argument but does not prove this arithmetic lemma. The detailed arithmetic source is the project Extension.lean:82–127, read in full, together with the Mathlib inputs. Thus the parent's existing proof_origin.by = agent is retained. The first new node refers to Extension.lean:84–109 and the arbitrary-extension spectral norm construction (SpectralNorm.lean:854–912); I read its normedField/normedAlgebra constructions and PadicNumbers.lean:815–823 for rational density, and Separable.lean:656–659 for characteristic-zero separability. The second refers to Extension.lean:110–126 and Approximation.lean:114–124 and 132–138, whose precise hypotheses I read. Krasner.lean:40–68 and the complete-space instance supply the last assembly. Where algebraic definitions/separability come from Stacks, the existing nodes use 09GC, 09H0 and 09H1; no Stacks tag purports to state the analytic approximation result.

For each new node I ran leanfinder (two different semantic phrasings), loogle, grep and leansearch through the mandated msearch command. I read all hits. First-node hits provide norm extension, separability or rational density separately, not the combined separation construction. Second-node hits are polynomial-root existence or coefficient bounds; its two genuine approximation inputs are separate existing leaves, and the tolerance, splitting and evaluation arguments intervene. Dense.lean:45–107 proves the different conclusion that a completion of an algebraically closed dense field is algebraically closed, not this node. Its proof has similar finite-gap calculations, which I read; it is not used as a black-box theorem. One leansearch request was rate-limited and is recorded unavailable. One grep given a file rather than directory produced malformed file labels; its raw output remains in the search log and the record explicitly declines to use it as attribution; the successful directory grep gives SpectralNorm.lean:854,908 correctly. Searches are recorded exactly as run with their actual raw result summaries.

DAG and whole-blueprint searches: blueprint_refs ancestor returned null, matching the inherited null-ancestor chain. Searches for minimal polynomial, dense subfield, Krasner, root approximation, conjugate and rational-algebraic gave no identical statement. I read the potential DAG overlaps listed below and searched project NumberTheory and FieldTheory source for the same concepts. The node's inherited unit is sk-thm-sf-ctf-stability; I read its unit and the sec-six-functors-basics chapter, and paragraph (3) of the main-20261015 direct-images proof. This arithmetic input remains below that paragraph through the inherited continuous algebraic-closure coefficient-comparison chain; I change no unit route and cite no SGA source.

## Not duplicates

lem-sfb-padic-minpoly-normed-separation vs lem-trf-spectral-norm-algebraic-extension: the latter supplies only the norm on a general algebraic extension; the new node includes characteristic-zero splitting minimal polynomials and an explicit positive conjugate gap in an arbitrary p-adic closure.
lem-sfb-padic-minpoly-normed-separation vs lem-pc-separable-polynomial-distinct-roots-alg-closed: the latter assumes separability and only gives the root factorization; it does not equip an arbitrary closure with a norm or construct the separation radius.
lem-sfb-padic-minpoly-normed-separation vs lem-per-henselian-krasner-neighbourhood: that node assumes a finite Galois valued extension and proves field membership; this node constructs the normed/minimal-polynomial data in an arbitrary closure and asserts no membership.
lem-sfb-dense-subfield-algebraic-root-approximation vs lem-sfb-monic-dense-approximation: coefficient approximation alone supplies neither a nearby root in L nor the arbitrary-radius estimate/algebraicity through the composite inclusion.
lem-sfb-dense-subfield-algebraic-root-approximation vs lem-sfb-roots-coefficient-proximity: the latter assumes two given polynomials with coefficient bounds and splitting, whereas the new node constructs a dense-subfield polynomial and derives its root and the explicit radius bound.
lem-sfb-dense-subfield-algebraic-root-approximation vs lem-per-henselian-simple-root-stability: the latter starts with a simple root in a henselian valued base and keeps a root in that base; the new node permits any monic polynomial root in an algebraically closed normed extension, with no separability/henselian/completeness assumption and a prescribed dense coefficient field.
lem-sfb-dense-subfield-algebraic-root-approximation vs lem-trf-separable-monic-approximation: that node perturbs within one valued field to make a polynomial separable; the new node changes the coefficient field and finds a nearby root, without asserting separability.
lem-sfb-padic-minpoly-normed-separation vs lem-sfb-padic-rational-algebraic-generator: no rational-algebraic element or simple-overfield membership is asserted by the new node; it carries only old steps 1–3.
lem-sfb-dense-subfield-algebraic-root-approximation vs lem-sfb-padic-rational-algebraic-generator: a nearby D-algebraic root is constructed for general D,K,L; it gives no K(b)-membership, which still requires the independent conjugate-gap and Krasner arguments.

## Review by Q95

I checked B–E against the new statements and every assembly step, rather than treating a successful check as mathematical review. Both new nodes introduce their own fields, norms, polynomial, element and radius, with definition references for algebraic closure, minimal polynomial, separability, roots and algebraic elements; neither contains proof steps or a hidden reference to an object in the parent's proof. Their norm and density conventions are explicit. The first does not assume the given closure is the canonical PadicAlgCl; spectral norm works for the actual given algebraic extension. The second does not assume a norm on D, or completeness of L: the coefficient approximation and root proximity statements need neither. Positive degree and a positive radius ensure M ≥ 1 and epsilon > 0. Field inclusions preserve monicity and degree, and the splitting argument removes a linear factor by division with remainder zero at a root until reaching the monic constant 1. Composite coefficient maps give the same finite evaluation sum, and monicity makes g nonzero. These are exactly the obligations retained from old steps 4–6.

Step 1 cites the new normed-separation node for every asserted datum: its statement explicitly gives the extending norm, complete/nontrivial/nonarchimedean base, rational density, f, n, splitting and delta. I verified its characteristic-zero requirement against Q_l and its algebraic-closure hypothesis against the actual Omega. Step 2 cites the new dense-root node, with D=Q, K=Q_l, L=Omega and r=delta. The inclusions are compatible by the unique prime-field map; step 1 gives density, f(x)=0 and positive degree/radius, and Omega is algebraically closed by the parent's hypothesis. That node's statement explicitly gives algebraicity over D and the strict distance bound; the step does not take anything only from its eventual proof. Step 3 cites the actual statement of def-weil-algebraic-closure for algebraicity of Omega/k, and the actual statement of lem-sfb-complete-normed-krasner for membership. I read both files: the latter needs the base complete and nontrivial, a norm extending it, a separable splitting minimal polynomial and strict inequalities to every other root, all supplied by steps 1–2. It does not require completeness of Omega. Every non-elementary assertion in the assembly is therefore covered by a cited statement, and citations.json uses verbatim statement text.

I tested x=0 and x in k (including x transcendental over Q): f has degree one and S is empty, so delta=1, not a minimum over the empty set. The final Krasner condition is vacuous, consistent with k contained in k(b). For degree n>1 separability gives finitely many distinct roots and each other-root distance is positive. In the second node I tested n=1 and a multiple-root polynomial: the first gives epsilon=r/(2M), and the second remains valid because proximity needs monicity/splitting, not separability. Very small or large r and x=0 leave M positive and the real-power equality valid. Degree zero is expressly excluded since a monic constant has no root. Both nodes are substantial separate source subarguments of comparable original length, not elementary new labels or either clause of the parent statement. No assembly step exceeds 2000 characters; the full parent proof is below 3000. No hollow definitions, unlogged searches, cycles, undeclared route changes, or altered target statements were introduced. The repair changes the dependency graph by adding the requested two nodes and retaining Krasner as the assembly tool.


## Landing refusal repaired: current live DAG rebase

The latest return is L's landing refusal: the earlier completion existed in the side DAG but had not been promoted into the live DAG read by the queue. This is distinct from the older proof-allocation return documented above. I continued the retained node files, report, citations and raw search log. The fresh delivery dry run rebuilds the delivery on the current server DAG and passed at 0f2d60a4c7e before these report/summary updates; a final dry run follows them.

I compared every retained item field with the current read clone. Only proof, proof_deps and split_report differ: the live node still has the original seven-step proof, whereas this delivery has the requested two new statement-only nodes and the short assembly. The statement, statement dependencies, source, blueprint provenance, Lean attachment and audit, historical searches, and review history agree with the live item and are retained. Neither new node id is present in the current DAG. The released stage-1 repair note still requires this re-split despite the older reviewed status. No changed definition or hypothesis requires a mathematical reroute.

I re-opened every current statement used by the assembly, including lem-sfb-complete-normed-krasner and def-weil-algebraic-closure. Their full retained citation quotes still match verbatim. The new-node statements also match their retained quotes, and every (step,node) citation is covered. I read the existing approximation and norm-extension input statements, the polynomial/algebraicity definitions, Extension.lean:76–127, Approximation.lean:114–138, Krasner.lean:63–68,117 and SpectralNorm.lean:854–912 again. The first new node supplies an extending norm on the given arbitrary closure, not merely on the canonical model. The second constructs a rational-algebraic nearby root without completeness of that closure. The algebraicity of the entire closure supplies Krasner's algebraic-extension hypothesis; its base completeness, nontriviality, nonarchimedean norm, separable splitting minimal polynomial and strict conjugate inequalities are all present. The degree-one empty-conjugate case remains valid. The assembled proof is 1194 characters, with no step above 2000.

The project search still finds only the canonical-model theorem in WeilConjectures/NumberTheory/Padics/Extension.lean; the arbitrary-closure statement in Sheaf/NumberTheory/Padics/RationalAlgebraicGenerator.lean remains sorry. The logged Mathlib queries and their actual hits were reread and reused because neither statement nor search question changed. The original proof allocation, complete original argument and Q95 mathematical review above remain applicable. This repair updates the delivery's live-DAG rebase record and split summary, and submits the substantive two-node re-split for promotion; it does not edit the live repository or any launcher tool.


## Rebase verification after resumed dispatch

The resumed check compared the retained split directly with the current shared read clone: exactly `proof`, `proof_deps` and `split_report` differ. Both new ids are still absent from that DAG. All statement, definition-dependency, provenance, search, Lean and historical review fields match the live item. The released repair note explicitly keeps the statement and requires two statement-only nodes, so its older reviewed status does not supersede this repair. The current-server dry run exited successfully at `d1f29742491`; no delivery invocation was left running before this report update. The final dry run and push below use the delivery tool's freshly fetched current server base.

I reread all four assembly citations and all definition statements of the two new nodes, together with the current monic-approximation, root-proximity, spectral-norm, derivative-separability and distinct-root input statements. Every retained citation quote remains verbatim and every assembly dependency is covered. In particular, Krasner assumes an algebraic extension, not merely an algebraic element x; the algebraic-closure definition supplies that hypothesis for the actual Omega. Root proximity does not require Omega to be complete or f to be separable; separability is needed only at the final Krasner application. The positive degree, norm restriction and explicit tolerance meet the exact hypotheses in Approximation.lean:114–138. I reread Extension.lean:76–127, Krasner.lean:40–70 and 111–143, SpectralNorm.lean:850–914 and Stanford L19 p.3. The latter invokes countability without proving this arithmetic argument, so the agent origin remains appropriate. The project's exact arbitrary-closure declaration still ends in `sorry`; the fixed-model source theorem does not replace the requested split.

This updates the rebase evidence rather than altering an already approved mathematical route. The two independent proof obligations, their original full arguments, the logged searches, the empty-conjugate and multiple-root checks, and the Q95 review are retained above. No claim is made that pushing itself promotes side completion: promotion remains L's landing action, for which this delivery supplies the current-base split.
