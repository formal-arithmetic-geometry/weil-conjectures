# Repair of lem-sfb-prime-to-ell-complete-scalar-integral

## Repair of the landing return (2026-10-22)

The current return is the landing refusal for returned head `f21da35c29dfbe969577093fc276d17dc9825bf7`: side completion had not been promoted into the live DAG used by the queue. This is distinct from the original granularity repair described below. I continued the retained sandbox, report, citations and searches; I did not recreate them. The required initial dry run exited successfully at `ccd7c96cd73` before any edit in this repair.

I compared the returned commit with current `origin/sheaf-dag` at `a6609deee6d15c9861b6fbf16ec18fba08359c0b` through the launcher's read-only commit-tree reader. The current item still has the original nine-step proof, and its released stage-1 repair note explicitly requires this re-split despite its old passing review. The item statement and all maintainer-owned fields agree with the returned head. All three extracted lemma files are absent from current main, so they remain three new nodes in this delivery. Their statements and logged searches are retained unchanged. The delivery tool builds on the latest origin and preserves its maintainer fields.

I re-read every existing cited statement and compared its complete node record against the returned head: `lem-sfb-dense-subspace-contractive-extension`, `def-weil-size-convention` and `def-weil-l-adic-numbers` are unchanged. I also re-read `lem-sfb-profinite-finite-map-approximation`, used in the retained density handoff; it too is unchanged. There are therefore no changed dependency hypotheses to propagate. I re-read the three sandbox lemma statements, the blueprint paragraph (3), the current Lean statement ending in sorry, and Mathlib's extension, finite-approximation, finite-average and curry declarations. Existing search results still answer the same questions, so no Mathlib search was repeated or invented.

The parent now explicitly identifies the density lemma's quotient-function set with the subspace D supplied by finite averaging before applying the extension theorem. This is the same set by their displayed definitions. Every one of the seven citation quotes remains verbatim. The parent assembly remains below 3000 characters, with every individual step below 2000; the three new nodes remain statement-only. The original nine steps and allocation below are retained in full. The final dry run and push are performed after these edits, rather than re-pushing the unchanged returned content.

1. Files written, all under the authorized sandbox:
   - `dag/nodes/sec-six-functors-basics/lem-sfb-prime-to-ell-complete-scalar-integral.json`: original statement unchanged; four-step assembly, 1854 characters; status split.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-finite-quotient-contractive-average.json`: statement, unsplit, no Mathlib match. Finite quotient compatibility and ultrametric averaging on the quotient-function subspace; no completion or parameter assertion.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-quotient-functions-dense.json`: statement, unsplit, no Mathlib match. Uniform approximation by open-normal quotient functions, without prime-to-ell or completeness assumptions.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-compact-parameter-functional.json`: statement, unsplit, no exact Mathlib match. Quantitative compact-section estimate and parameterwise module operation for an already given arbitrary contraction; it constructs no invariant integral.
   - `citations.json`, `searches.jsonl`, this report, and sandbox-only repair scripts and returned-item.json retaining the original node.
2. Attachments: none. Read the tagged source theorem `WeilConjectures.primeToEll_completeScalar_integral`, `lean/Sheaf/Analysis/PrimeToEllCompleteScalarIntegral.lean:62`, whose body is `sorry`. Searches of `lean/WeilConjectures/` by the blueprint id, declaration name, prime-to-ell integration, quotient averaging and linear-functional notions gave no exact finished declaration. Existing upstream declarations with sorry are not attachments.
3. WANTED: an exact human-written reference for nonarchimedean normalized integration on pro-prime-to-ell groups, and its compact-parameter argument, for the item and the three new nodes. The blueprint paragraph (3) supplies the geometric context only; it does not assert or prove these analytic inputs. No SGA source is used.
4. The return concerns granularity, not a false statement. The live node contains the returned nine-step proof. There were no retained node, report or search files in the sandbox, only dispatcher marker files; therefore the live node was copied and its existing citations, logged-search summaries, statement, audit and review metadata were retained. No user statement or target was changed. No source error or route change was found.
5. All mathematical work requested by the return is complete. Delivery verification is recorded below after the tool exits. No Lean was written or compiler, Lake or build command run.

## Earlier re-split requirement (retained history)

The single returned requirement asks for at least two comparable new independent statement-only tasks and a parent assembly of at most 3000 characters. This repair adds three such tasks, each status unsplit with empty proof and proof_deps and null proof_origin. Their expected arguments are roughly 2100, 1350 and 1770 characters from the retained proof; none restates the whole integral theorem. The parent is 1854 characters. Nothing mathematical was dropped: old steps 1–3 belong to finite-quotient-contractive-average, old steps 4–5 to quotient-functions-dense, old steps 6–7 remain in parent assembly steps 2–3, and old steps 8–9 belong to compact-parameter-functional. Old step 9's universe convention is also explicit in the parent. The complete original steps are retained verbatim below, as the workers' starting arguments; they are not placed in unsplit node statements as proof sketches.

## Sources and argument handoff

Read the chapter record `sec-six-functors-basics`, unit record `sk-thm-sf-ctf-stability`, the current main-20261015 direct-image stability proof and the live item with all nine steps. Its paragraph (3) treats proper and open direct images before compactification. The analytic tame-kernel lemmas are agent expansions below this route, rather than a replacement for it. There is no imported ancestor: `tools/blueprint_refs.py ancestor` prints None; the null ancestor and inherited via chain are retained, and each new node prefixes its parent id to that chain with the exact extraction place. The chapter and unit records are untouched.

For finite-quotient-contractive-average the source is the analytic expansion of returned steps 1–3, reproduced below. A future worker proves finite index by compactness, makes a subspace by common refinements, counts each refinement fibre as |U/V|, and reindexes sums. Norm-one prime-to-ell denominators follow from `def-weil-l-adic-numbers` and the isometric inclusion; the strong triangle inequality gives the contraction. No completeness is needed here.

For quotient-functions-dense the source is returned steps 4–5 below. First cosets are clopen and separate points, proving total disconnectedness. The existing node `lem-sfb-profinite-finite-map-approximation` states finite discrete approximation for compact Hausdorff totally disconnected spaces. I read its full statement and Mathlib `Topology/Separation/DisjointCover.lean:140–141`: the open diagonal neighbourhood |b-c|<epsilon/2 is allowed. Finite subcovers of constant-fibre cosets and their subgroup intersection give a common open-normal quotient. This normal-coset refinement is required in addition to the Mathlib finite-map theorem. The new statement explicitly includes the finite-discrete factorization property. A future worker can also cite the existing open-stabilizer node for that subargument, rather than create a duplicate of it.

For compact-parameter-functional the source is returned steps 8–9 below, with I_K replaced by any given contraction L and K by a nonempty compact Hausdorff X. The product-neighbourhood finite-subcover estimate proves the stated epsilon/2 bounds. Pointwise linearity gives the continuous-function module law; evaluation after u times id gives naturality. Empty sums and empty parameter spaces are included. Completeness, nonarchimedeanness, the group structure and normalization are not used, so none is imposed.

The old proof text remains below in full; the new unsplit nodes carry self-contained propositions rather than their proofs. Each new source names its exact old step range honestly as an agent expansion, and every object used in each statement is introduced there.

## Searches and Mathlib verdicts

All new-node Mathlib searches were made by the prescribed msearch.py command with group Q97 and this item. Their exact query text and returned metadata are in the node files and searches.jsonl. Both semantic phrasings were read; some LeanSearch calls were initially rate-limited and are recorded unavailable, followed by successful calls with a different phrasing. No unavailable result is used as evidence of absence. Existing item search records are retained unchanged, and their top hits were reread.

Finite averaging searches returned real-valued Haar, Foelner and Birkhoff results, and `Representation.averageMap`. I read `RepresentationTheory/Invariants.lean:129–147`: it constructs a projection for a fixed finite representation with invertible group order, not compatible averages across quotient refinements on D, and it gives no ultrametric bound. These do not close the auxiliary lemma in one specialization.

Density searches returned LocallyConstant, quotient-density statements and profinite inverse-limit structure. None gives density of the union of finite group-quotient functions. The known finite-map approximation leaf is an input, not the whole argument: the open-normal refinement must still be proved. `LocallyConstant.continuous` and quotient-density results are not uniform approximation results.

Parameter searches returned `ContinuousMap.curry`, evalCLM and CLM postcomposition constructions. I read `Topology/CompactOpen.lean:430–435`; currying is continuous for compact-open topology. It neither states the quantitative supremum estimate in the new node nor the complete C(P,B)-module and naturality package. This new lemma is the explicit compact-section argument plus pointwise operation laws; those candidates are useful when it is later split, but are not an exact or one-line specialization covering the statement. No bespoke Mathlib leaf was invented.

DAG searches covered both whole-file keyword matches and statement-only scans throughout dag/nodes, so matches inside unrelated proofs were not mistaken for declarations. Blueprint searches: `finite quotient averaging`, `dense profinite functions`, `parameter continuous linear functional`, `nonarchimedean`, `finite approximation` gave zero imported matches; `curry` returned five derived/sheaf-kernel or projection-formula nodes, not compact-function analysis. Lean source searches likewise gave no exact project statement for the new nodes.

## Not duplicates

lem-sfb-finite-quotient-contractive-average vs lem-sfb-prime-to-ell-complete-scalar-integral: this constructs a functional only on finite-quotient functions, with no density, extension to all continuous functions or parameters; the parent still needs a separate density proof and complete-target extension.

lem-sfb-quotient-functions-dense vs lem-sfb-profinite-finite-map-approximation: the existing node approximates through an arbitrary finite discrete set on a totally disconnected space; the new node derives total disconnectedness from the open-normal basis and gives approximation through a finite group quotient, with explicit normal-coset refinement.

lem-sfb-quotient-functions-dense vs lem-exc-coinduced-functions-open-stabilizer: the latter factors a continuous discrete-valued function through open cosets; it gives neither continuous normed-field approximation nor norm density. Its statement can serve the discrete-factorization subargument in the future split.

lem-sfb-quotient-functions-dense vs lem-sfb-profinite-metric-function-quotients: the latter factors a continuous map through a metrizable profinite quotient, which may be infinite; it does not give finite-quotient uniform approximation.

lem-sfb-compact-parameter-functional vs lem-sfb-prime-to-ell-complete-scalar-integral: this starts with an arbitrary given linear contraction on an arbitrary nonempty compact Hausdorff space, and proves the quantitative parameter statement; it proves no existence, normalization, finite-quotient formula or translation invariance of an integral.

lem-sfb-finite-quotient-contractive-average vs lem-sfb-finite-index-rectangle-primitive-operator: the latter constructs a cochain primitive from vanishing on a coset rectangle, with a finite-index norm loss; it does not define compatible normalized quotient averages on D.

No Stacks tag is used as the source of a new analytic assertion; there are no same-tag pairs requiring additional distinctions.

## Review by Q97

For this landing repair I compared the exact returned head and current main as recorded above. No existing cited node changed. Step 1 still takes only finite-level averaging, not the whole integral, from the new finite-average statement. Step 2 now makes the equality of the two definitions of D explicit; density and the complete target B give precisely the hypotheses of the unchanged extension statement. Step 3 uses the same finite-average translation laws and extension uniqueness, and step 4 uses the parameter lemma with nonempty compact Hausdorff X=K and L=I_K. I checked again the trivial and finite K cases, empty parameter spaces and sums, and that no completeness assumption was introduced on the dense domain. The blueprint still provides context only, with the exact analytic reference honestly WANTED. This repair changes the assembly explanation and its report, while retaining the three separately actionable new tasks, source handoff and actual logged searches.

I reread delivery-errors B–E in full and checked the actual files and cited statements. B1–B2: each new node is statement-only, introduces all objects and hypotheses, and has no proof steps or proof sketches. B3: all nonstandard coefficient and size conventions are cited explicitly; normed fields, function spaces, the basis condition, profinite spaces, quotient functions, translations and the parameter scalar action are defined inline. B4: TeX was written once and serialized through json.dump. B5–B8: no section number is substituted for a Stacks tag, no Stacks source is claimed for these agent inputs, no new Mathlib match or line claim is asserted, and actual msearch results are preserved. B9–B10: the ancestor and blueprint searches were made, and the only exact project declaration of the parent is visibly sorry.

For parent step 1 I opened finite-quotient-contractive-average: its statement gives exactly D as a linear subspace, compatibility, the finite formula, A(1), the norm bound and both finite-level translation laws. Its coefficient and quotient hypotheses are precisely those of the parent; all quotients are finite by compactness, and an isometric Q_ell inclusion supplies characteristic zero and unit norm of each denominator. Step 1 does not use anything inside that node's future proof.

For parent step 2 I opened quotient-functions-dense, whose D is exactly the same set and whose statement gives norm density. Its B need not be complete, so our complete B certainly qualifies. I reread the whole existing dense-subspace-contractive-extension statement: it gives an extension agreeing on D, a norm bound and uniqueness, requires only complete target F and no complete domain. Substituting k=B, E=C(K,B), F=B, D and A meets every hypothesis. I checked the supremum norm is finite by compactness and the field norm gives its linear-space inequalities pointwise.

For parent step 3 I again checked the finite-average statement actually includes preservation of D and invariance there, and the extension node explicitly says unique continuous linear extension. The precomposition operators are isometries because translation and its inverse are continuous bijections; no assumption of commutativity of K is made. Equality of two extensions is the exact uniqueness conclusion, not an unrecorded Haar theorem.

For parent step 4 I opened compact-parameter-functional and checked every output: continuity, C(P,B)-linearity, finite sums and precomposition, including empty cases. It only asks for a given contraction on C(X,B), which step 2 supplied. A group is nonempty, and the parent's compact Hausdorff K satisfies the X hypotheses. The size citation is only used for the same inherited universe convention. All seven citations (counting repetitions between steps) have full verbatim statement quotes in citations.json. No definition-only node is cited for an analytic theorem.

C1–C4: all non-elementary assertions in the parent are explicit cited statements; the remaining sup-norm and translation calculations are written out. No proof of a cited node is silently used. C5–C8: the whole-DAG and blueprint searches found no exact duplicate; dependencies point downward, and there is no off-unit statement route change. The generic extension node is a Mathlib leaf and needs no off-route authorization. D1–D5: three distinct arguments were extracted, with strictly different hypotheses and outputs; no single new node contains the whole integral theorem, and the parent still performs the complete-space extension and translation argument. The explicit return authorizes extracting these old arguments even when some individual substeps are elementary.

I tested E1–E6 on K trivial, finite K of order prime to ell, U=K and V=U. The averaging formula reduces to evaluation or the expected finite mean; no quotient is empty and |Q| is nonzero. If ell divides a quotient order, the characteristic-function average can have norm greater than one, confirming the prime-to-ell hypothesis is essential rather than omitted. Density works for an arbitrary normed B and does not use a countable normal basis; its finite-discrete assertion is vacuous for an empty target, since K is nonempty. Parameter continuity uses compactness of X, not compactness of the field; the zero functional, empty P/P' and empty sum satisfy all claims. The epsilon/2 bound is obtained by a strict pointwise bound followed by a non-strict supremum bound, leaving the strict epsilon margin. No statement needed correction against its intended source (E7).

No parent proof step exceeds 2000 characters. All nine old arguments remain below, assigned to separate nodes or the parent rather than shortened away. This is my review signature for the repair, not a claim of independent review.

## Full retained proof and allocation

### Returned step 1 → lem-sfb-finite-quotient-contractive-average

For each open normal subgroup $U$, the open cosets cover compact $K$, hence a finite subcover contains every coset; thus $Q_U=K/U$ is finite and nonempty. Let $D\subseteq C(K,B)$ consist of the functions factoring through some $Q_U$. These are continuous because cosets are open. Intersecting two open normal subgroups gives another such subgroup, and both quotient maps factor through its quotient. Consequently pointwise sums and scalar multiples make $D$ a $B$-linear subspace; constant functions belong to it. Write $A_U(\bar f)=|Q_U|^{-1}\sum_{q\in Q_U}\bar f(q)$ for the proposed average of a function factoring through $Q_U$. The denominators are nonzero because $B$ contains the characteristic-zero field $\mathbf Q_\ell$.

Cited nodes: none (elementary)

### Returned step 2 → lem-sfb-finite-quotient-contractive-average

Suppose $V\subseteq U$ are open normal subgroups. The map $Q_V\to Q_U$ is onto and each fibre has $t=|U/V|$ points: choose a representative $a$ of a coset of $U$; the bijection $U/V\to aU/V$ is $uV\mapsto auV$. Partitioning the finite sum by these fibres gives $|Q_V|=t|Q_U|$ and
$$|Q_V|^{-1}\sum_{z\in Q_V}\bar f(z\bmod U)=(t|Q_U|)^{-1}t\sum_{q\in Q_U}\bar f(q)=A_U(\bar f).$$
For two arbitrary choices $U_1,U_2$ through which the same function factors, apply this identity to $V=U_1\cap U_2$. The descended functions on $Q_V$ agree since $K\to Q_V$ is onto. Thus $A:D\to B$ is well defined. Computing two functions on a common quotient proves additivity and $B$-homogeneity term by term.

Cited nodes: none (elementary)

### Returned step 3 → lem-sfb-finite-quotient-contractive-average

For $n=|Q_U|$, the prime-to-$\ell$ hypothesis gives $v_\ell(n)=0$ directly from the valuation formula of [def-weil-l-adic-numbers]. Thus $|n|_B=|n|_\ell=1$ by the isometric inclusion, and $|n^{-1}|_B=1$ by multiplicativity. Induction on the finite number of summands using the strong triangle inequality gives
$$|A(f)|\leq\max_{q\in Q_U}|\bar f(q)|=\|f\|_\infty.$$
Also $A(1)=n^{-1}n=1$. For $a\in K$, normality of $U$ makes both $q\mapsto aq$ and $q\mapsto qa$ permutations of $Q_U$. Reindexing the finite sum proves $A(f(a\cdot))=A(f)=A(f(\cdot a))$. The norm identity uses only the definition of the valuation, rather than introducing a separate node for a prime-to-$\ell$ integer.

Cited nodes: def-weil-l-adic-numbers

### Returned step 4 → lem-sfb-quotient-functions-dense

The open normal subgroups and their cosets are clopen: the complement of a coset is the union of all other open cosets. They separate distinct points by Hausdorffness and the assumed identity-neighbourhood basis. A connected subset containing two distinct points would therefore be separated by a clopen coset. Hence $K$ is totally disconnected. Given $f\in C(K,B)$ and $\epsilon>0$, apply [lem-sfb-profinite-finite-map-approximation] with $X=K$, $V=B$ and the open neighbourhood $S=\{(b,c):|b-c|<\epsilon/2\}$ of the diagonal. Obtain continuous $g:K\to\operatorname{Fin}(n)$ and $h$ with $|f(x)-h(g(x))|<\epsilon/2$. Put $d=h\circ g$, which is continuous since the intermediate space is discrete. We next check explicitly that $d\in D$, so that these approximations prove norm density.

Cited nodes: lem-sfb-profinite-finite-map-approximation

### Returned step 5 → lem-sfb-quotient-functions-dense

For each $x\in K$, the open fibre $g^{-1}(g(x))$ contains $xU_x$ for some open normal subgroup $U_x$, by the identity-neighbourhood basis translated by $x$. Choose a finite subcover $x_iU_{x_i}$ of $K$, and put $U=\bigcap_iU_{x_i}$. If $y\in x_iU_{x_i}$ and $u\in U$, then $yu\in x_iU_{x_i}$, so $g(yu)=g(y)$. Thus $g$, and therefore $d$, is constant on every coset $yU$, giving $d\in D$. The pointwise approximation implies $\|f-d\|_\infty\leq\epsilon/2<\epsilon$. This proves density for every $f,\epsilon$, without a countable basis or metrizability assumption on $K$.

Cited nodes: none (elementary)

### Returned step 6 → parent assembly step 2

Apply [lem-sfb-dense-subspace-contractive-extension] with scalar field $k=B$, normed space $E=C(K,B)$, complete target $F=B$, dense subspace $D$ from steps 1 and 4–5, and $u=A$ from steps 2–3. The supremum norm is the norm stipulated in the statement; its triangle inequality and scalar homogeneity follow pointwise from those in $B$. Completeness is required only for the target $B$, which is a hypothesis of the item. This produces a continuous $B$-linear extension $I_K$ with $|I_K(f)|\leq\|f\|_\infty$. Its agreement with $A$ gives the required formula on every $K/U$, in particular $I_K(1)=1$.

Cited nodes: lem-sfb-dense-subspace-contractive-extension

### Returned step 7 → parent assembly step 3

Fix $a\in K$. The maps $T_a^Lf(h)=f(ah)$ and $T_a^Rf(h)=f(ha)$ are $B$-linear isometries of $C(K,B)$: translations are continuous bijections with continuous inverse, and each supremum is over all of $K$. They preserve $D$, and step 3 shows that the continuous linear maps $I_K\circ T_a^L$ and $I_K\circ T_a^R$ both restrict to $A$ there. The uniqueness clause of [lem-sfb-dense-subspace-contractive-extension], applied to the same $D,A,E,F$, identifies both with $I_K$. This proves both translation identities on all continuous functions.

Cited nodes: lem-sfb-dense-subspace-contractive-extension

### Returned step 8 → lem-sfb-compact-parameter-functional

Let $P$ be profinite and $f:P\times K\to B$ continuous. Define $J_P(f)(p)=I_K(f(p,-))$; each section $f(p,-)$ is continuous by restriction of $f$. To prove continuity fix $p_0\in P$ and $\epsilon>0$. The function $d(p,h)=f(p,h)-f(p_0,h)$ is continuous and $d(p_0,h)=0$. For each $h\in K$, continuity gives product neighbourhoods $V_h$ of $p_0$ and $W_h$ of $h$ on which $|d|<\epsilon/2$. Choose finitely many $W_{h_i}$ covering compact $K$, and take $V=\bigcap_iV_{h_i}$. For $p\in V$, every $h$ belongs to one of these $W_{h_i}$, so $\|f(p,-)-f(p_0,-)\|_\infty\leq\epsilon/2$. By linearity and the bound from step 6,
$$|J_P(f)(p)-J_P(f)(p_0)|\leq\|f(p,-)-f(p_0,-)\|_\infty\leq\epsilon/2<\epsilon.$$
This is continuity at $p_0$. For $P=\varnothing$ the assertion is vacuous. This finite-subcover argument checks the parameter topology directly; it assumes neither local compactness of $B$ nor metrizability of $P$ or $K$.

Cited nodes: none (elementary)

### Returned step 9 → lem-sfb-compact-parameter-functional

For $c\in C(P,B)$, evaluate at $p$: $J_P(cf)(p)=I_K(c(p)f(p,-))=c(p)I_K(f(p,-))$. Likewise $J_P(f_1+f_2)(p)=J_P(f_1)(p)+J_P(f_2)(p)$ and $J_P(0)=0$, by the established $B$-linearity. The products and sums here are continuous by continuity of the field operations, and step 8 ensures the outputs lie in $C(P,B)$. Thus $J_P$ is $C(P,B)$-linear and commutes with finite sums, including the empty sum. For any continuous $u:P'\to P$ the equality
$$J_{P'}(f\circ(u\times\mathrm{id}_K))(p')=I_K(f(u(p'),-))=(J_P(f)\circ u)(p')$$
holds by the defining evaluation formula. Precomposition preserves continuity because composites of continuous maps are continuous. Equality at every $p'$ proves naturality, also for an empty source. All function sets, finite quotients and their subspaces are taken inside the universes fixed by [def-weil-size-convention].

Cited nodes: def-weil-size-convention

## Earlier validation (retained history)

Required deliver.py --no-push completed successfully with exit 0: OK (not pushed), preflight passed, candidate 9ecca8eb474. This runs the maintainer preflight, check_dag and review_split on the server. Local source-only checks confirmed statement equality, unchanged maintainer metadata, 1854 parent proof characters, empty proofs on all three new unsplit nodes, and verbatim retention of all nine original steps. The authorized final push follows; its commit is reported in the final delivery response.
