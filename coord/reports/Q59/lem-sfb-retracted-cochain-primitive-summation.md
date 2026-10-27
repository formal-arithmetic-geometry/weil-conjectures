# Q59 stage-1 delivery: lem-sfb-retracted-cochain-primitive-summation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-retracted-cochain-primitive-summation.json`: item, now split, with unchanged statement and statement dependencies. Nine explicit steps prove the retraction correction, bound, assembly, pointwise vanishing, uniform convergence, continuity and actual coboundary equality.
- `dag/nodes/sec-six-functors-basics/lem-sfb-metric-completion-isometry.json`: statement, Mathlib leaf, exactly `UniformSpace.Completion.coe_isometry`, `Mathlib/Topology/MetricSpace/Completion.lean:157–158`, specialized to normed Q_l-vector spaces.
- `citations.json`: verbatim statement quotes for the completion-isometry citation in steps 8 and 9.
- `searches.jsonl`: the actual msearch log.

## Attachments

None. I searched the upstream project `lean/WeilConjectures/` by the item's blueprint tag and by retraction/cochain, primitive/cochain, stabilizing-selector and pointwise-vanishing terminology. No declaration states the item. The local `Sheaf/RepresentationTheory/ParameterCochainCompletionBoundaryDescent.lean` contains the ancestor's thirteen-step argument in a docstring, not a finished project declaration proving this item. That text is useful source material only. The Mathlib completion theorem is recorded as a Mathlib leaf, not as a project attachment.

## WANTED

WANTED: an external reference for the retraction-corrected finite-evaluation primitive assembly and incomplete-coefficient summation argument, for `lem-sfb-retracted-cochain-primitive-summation`. The blueprint direct-images paragraph (3) does not assert this analytic lemma. Accordingly the proof is honestly marked agent-written; no Stacks or other literature theorem is invented. The one new foundational input is supplied by the exact Mathlib source read below.

## What needed repair

At the original attempt the item was unsplit, with no proof and no existing sandbox attempt. No statement error was found. I preserved the range `1 <= j <= i`, which is essential to the hypothesis on `d(T_j e_i)`; there is no assertion for j > i. The statement's assumptions on closed covers, retractions and selectors are inputs, not existence results needing re-proving here.

The proof now explicitly writes `B = c - v composed with rho`. This gives the sharp ultrametric bound without an unnecessary factor 2. The fact that the differential changes no parameter coordinate is checked term by term, both for retraction pullback and for the locally constant choice. Eventual vanishing uses the eventually fixed index j(s), so that the evaluation list is fixed before the finite maximum of thresholds is taken.

For summation I define the limit directly as the eventual finite value in V. The bound on each finite tail gives uniform convergence in V itself, then an epsilon argument gives continuity in its original topology. This is the same finite-value argument as the inherited proof, with the order of its elementary deductions made explicit. It does not assume V is a field, complete, finite dimensional, or that the pointwise vanishing thresholds are uniform in s or x. The completion is used only to identify the stated limits and recover z from the assumed convergence of the e_i sums.

Nothing remains unfinished in this split. The requested exact external literature reference remains WANTED. There is no re-split repair order for this item, and no argument has been transferred to a new unsplit node.

## Searches and source checks

I read AGENTS.md, GOAL.md, the worker brief and role, the stage-1 document, the three levels in SETUP.md, the chapter and unit records, and delivery-errors B–E (including the duplicated isolated-run sections). I read the current main-20261015 direct-images proof paragraph (3), and the old steps 11–13 retained in the ancestor's Lean docstring at `lean/Sheaf/RepresentationTheory/ParameterCochainCompletionBoundaryDescent.lean:154–185`.

Whole-DAG searches covered metric-completion/isometry, normed-group completion, uniform series and pointwise-finite cochains. The blueprint searches were `uniform convergence`, `completion`, `isometry`, `retraction`, `summation`, `cochain`, `metric completion` and `primitive summation`; no blueprint node states either this item or the normed-vector-space isometry leaf. `blueprint_refs.py ancestor` gives None, as the inherited item already records; the new leaf retains this null ancestor and prepends the item to the inherited via chain, with an explicit paragraph and old-step place.

All fresh Mathlib searches were run through msearch.py and read. For the item I used two distinct semantic phrasings, Loogle on continuous cohomology, the logged cochain/retraction/pointwise/summability grep, and LeanSearch. The approximation and Mahler hits do not prove the retraction correction. I read `Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean:15–43`: it defines homogeneous continuous cochains and cohomology, and does not state this primitive assembly. I read `Mathlib/Analysis/Normed/Group/FunctionSeries.lean:28–53`: its generic summation result assumes a complete NormedAddCommGroup, and would not alone supply the return of the limit to V or pointwise eventual vanishing. It is not an exact match for the item.

For the new leaf, LeanSearch, LeanFinder and Loogle all returned `UniformSpace.Completion.coe_isometry`. The successful directory grep locates it at `Mathlib/Topology/MetricSpace/Completion.lean:157`. I read lines 130–168: the completion's metric structure precedes the exact isometry theorem at 157–158. I also read `Topology/UniformSpace/Completion.lean:282–306`, including the actual Cauchy-filter/separation-quotient completion construction and completeSpace instance. Only the distance identity, not completeness or any extension-of-operators theorem, is used by the item. The coefficient field in the final leaf statement is defined by def-weil-l-adic-numbers, whose statement I read; it supplies Q_l, and does not claim that the vector space V is complete. The initial single-file grep omitted the filename in rg's output; its result is retained honestly in searches.jsonl, and I reran grep on the containing directory to obtain the actual filename and line. The leaf records the latter successful source-location search.

## Not duplicates

lem-sfb-metric-completion-isometry vs lem-sfb-normed-field-completion: the existing statement assumes a normed field and constructs its completed field and ring homomorphism; the new leaf applies to any normed Q_l-vector space; Mathlib itself states the more general metric-space theorem. The item's V is only a normed vector space and has no field structure, so the existing statement cannot supply its completion embedding. This is a genuinely more general existing Mathlib theorem, not a new special case of that node.

lem-sfb-metric-completion-isometry vs lem-wf-dominated-continuous-function-series: the latter concerns uniformly dominated series with complete field target and says nothing about metric completion embeddings. We construct our finite-value limit and prove continuity in the item's own steps; no new node restates its series clause.

lem-sfb-metric-completion-isometry vs lem-sfb-retracted-cochain-primitive-summation: the leaf contains no cochains, retractions, selectors or series. It supplies the foundational distance identity used only after the item's construction and estimates have been proved inline. The item's substantive retraction and pointwise-finiteness claims remain proved in the item.

## Review by Q59

I checked the split against the actual hypotheses, not merely the shape of the JSON. The analytical source is the agent-written ancestor argument, whose steps 11–13 are preserved verbatim below, together with the current blueprint paragraph (3) as context. The new leaf's source is the actual Mathlib metric-completion theorem at lines 157–158; its statement is the distance identity that theorem gives, rather than a claim about field completions. There are no SGA citations or nonanalytic route replacements.

Step 1 uses only the displayed finite formulas and continuity of the given maps. Writing out d after substituting rho gives the same rho in every term; no equivariance or homotopy theorem is being assumed. Step 2 uses precisely the hypothesis `d(T_j e_i)(a,-) = e_i(a,-)` for a in A_j and j <= i. Since rho_j(s) lies in A_j, the pullback of dv is zero. The retraction identity on A_j gives the asserted restriction. Step 3 uses the given operator bound and the strong triangle inequality; rewriting B as c - Rv is what preserves the claimed maximum bound.

Step 4 proves continuity locally where the selector is constant, and observes that all differential faces keep the same s, so there are no boundary terms in s. It checks C_j <= D_i, D_i >= 1 and the shared smallness hypothesis, and treats b_0 separately. Step 5 fixes s,x first and then j(s); only after stabilization is the finite list of evaluation points fixed. Taking the maximum of finitely many vanishing indices is elementary and requires no uniform vanishing hypothesis.

Step 6 chooses a point-dependent cutoff only to express the difference as a finite sum. The numerical bound 2^(-N) is independent of that cutoff and of the point, so the convergence really is uniform. Step 7 supplies the neighbourhood and strict epsilon inequality rather than quoting an uncited uniform-limit theorem. Step 8 cites the new leaf; I reopened its statement and copied the entire distance-identity sentence into citations.json. It applies to V because a norm is a separated metric, without any completeness requirement. This produces the completed convergence by the identical distance estimate. Step 9 cites the same leaf for injectivity (distance zero implies equality) and otherwise uses only a finite common threshold over the differential's faces, linearity and the stated convergence of the e_i sums. In particular it proves an equality of actual V-valued cochains, not an equality modulo closure of boundaries. The quote in citations.json is verbatim for both uses, and all proof_deps equal the union of the step uses.

Small cases checked: V = 0; singleton S and the trivial group; n = 2 (the smallest permitted primitive degree); zero e_i and c_i; j = i; u_j = 0; repeated A_j and arbitrary selector behaviour before eventual stabilization; nonzero unrestricted c_0; cutoffs below a chosen partial-sum index; and noncomplete normed V. The finite-tail formula takes a cutoff at least N, so the zero-tail case is valid. No division, nonzero vector, positive dimension, completeness, group commutativity, or uniform selector threshold is used. All steps are under 1000 characters, so none hides a long independent comparison lemma. The new leaf is statement-only, with no proof dependencies; all its recorded queries were actually run, and the source location is read from the logged grep. The item statement and original imports/metadata are retained.

## Inherited source argument, retained verbatim

The following is the relevant original argument from the ancestor's docstring. Its field symbols belong to that ancestor; the item already generalizes the analytic calculation to V and assumes the resulting operator and smallness hypotheses.

```text
11. For $i\geq1$ and $j\leq i$ put $v_{i,j}=c_i-T_je_i$ and define
$$B_{i,j}(s,x)=(T_je_i)(s,x)+v_{i,j}(s,x)-v_{i,j}(\rho_j(s),x).$$
These are continuous
$F_{L_i}$-valued cochains. At $a\in A_j$, the homogeneous values of $z(a,-)$ on $B_j$ lie in
$F_{N_j}$, which both $P_i$ and $P_{i-1}$ fix since $L_{i-1}\geq N_j$. Thus the homogeneous
function of $e_i(a,-)$ vanishes there. The rectangle operator gives $dT_je_i(a,-)=e_i(a,-)$, so
$dv_{i,j}(a,-)=0$. Therefore
$$dB_{i,j}=dT_je_i+(e_i-dT_je_i)-0=e_i.$$
Also
$B_{i,j}(s,-)=T_je_i(s,-)$ for $s\in A_j$, because $\rho_j(s)=s$. Its supremum norm is at most
$\max(\|c_i\|_\infty,C_j\|e_i\|_\infty)$, by the ultrametric inequality and the operator bound.

12. Let $b_0=c_0$. For $i\geq1$ define $b_i(s,x)=B_{i,k_i(s)}(s,x)$. The finitely many clopen
pieces of $k_i$ make this a continuous $F_{L_i}$-valued cochain with $db_i=e_i$. Since
$k_i(s)\leq i$, the preceding bound and $D_i\max(\delta_i,\delta_{i-1})\leq2^{-(i-1)}$ give
$\|b_i\|_\infty\leq2^{-(i-1)}$. Here $D_i\delta_{i-1}=2^{-(i-1)}$ and $D_i\delta_i\leq2^{-i}$.
Fix $(s,x)$. Eventually $k_i(s)=j(s)$ and $s\in A_{j(s)}$, so
$$b_i(s,x)=T_{j(s)}e_i(s,x)=\sum_{a=1}^{u_{j(s)}}\alpha_{j(s),a}e_i(s,\psi_{j(s),a}(x)).$$
This
is one fixed finite list of evaluations. Each term is eventually zero by step 10. Hence
$b_i(s,x)=0$ for all sufficiently large $i$.

13. The partial sums $\sum_{i=0}^Nb_i$ are uniformly Cauchy into the complete field $B$: by the
ultrametric inequality every tail has norm at most the largest norm of its terms, and those
norms tend to zero. Their pointwise limits therefore give a uniform limit $b_*:S\times
G^{n-1}\to B$. For continuity, approximate $b_*$ uniformly within any prescribed positive error
by one continuous partial sum and use the strong triangle inequality near the point in question.
Step 12 makes every value a finite sum in $\Omega$; the isometric subspace topology then makes
$b_*$ continuous into $\Omega$ itself. At a fixed input $d$ is a finite sum of evaluations, so
$$db_*=\lim_Nd\Big(\sum_{i=0}^Nb_i\Big)=\lim_NP_Nz=z.$$
Pull back this cochain by $p\times
q^{n-1}$ from step 2. It is a genuine $\Omega$-valued continuous primitive on the original $S$.
Choose $S_1=S$, $u_1=\mathrm{id}_S$. This proves the requested assertion with actual equality of
cochains.
```

## Dry-run repair

The first server dry run rejected the new leaf because its generic metric-space statement cited no DAG notion. No metric-space or normed-space definition node exists in the DAG. I stated the needed one-line specialization for normed Q_l-vector spaces instead, with the genuine statement dependency def-weil-l-adic-numbers for its scalar field, rather than adding an unrelated citation. The item still has exactly the same proof and statement; the new leaf still follows directly from the same Mathlib theorem. The citation quotes were updated to its exact distance formula.

## Returned delivery repair — 2026-10-23

The return entry in coord/returns/Q59.md identifies returned head `13626ca96eb` and says that the independent reader approved it, but landing refused the side-project completion. This sandbox retains that delivered split, report, citations and original search log. I continued those files rather than replacing their proof or repeating searches whose questions have not changed.

I compared both sandbox node files with the current read-only DAG. The live item remains unsplit. Its statement, statement dependencies, title, source, created record, chapter, unit and blueprint references agree exactly with the retained item. The differences are the nine proof steps, proof dependency, proof origin, split report, split status and five supplemental executed searches. The metric-completion-isometry leaf is still absent from the live DAG. Thus no live mathematical change requires a replacement dependency or a different construction. The delivery tool builds the repair on the current origin/sheaf-dag and preserves current maintainer-owned fields; the initial required dry run completed successfully at `448b6e9db80` before these repair edits.

I re-read every statement used here: the scalar definition def-weil-l-adic-numbers defines the required Q_l; def-weil-size-convention supplies the universe convention; and the retained leaf gives exactly the distance identity quoted in citations.json for steps 8 and 9. I also reopened Mathlib/Topology/MetricSpace/Completion.lean:130–168, including coe_isometry at 157–158, and the ancestor's original argument at Sheaf/RepresentationTheory/ParameterCochainCompletionBoundaryDescent.lean:154–185. No changed scalar or completion hypothesis affects the split. The current whole-DAG completion search found the normed-field completion and pointwise-finite series nodes; I read their statements, and both require the coefficient object to be a field, whereas this item allows arbitrary normed Q_l-vector spaces. They cannot replace the vector-space completion leaf. The new leaf is not an additional summation lemma. The current upstream declaration search again found no exact project attachment.

I adjusted proof step 9 to make its final implication explicit: after taking a common finite threshold for the differential evaluations, choose the partial-sum index also past the completed-series convergence threshold. The quoted isometry makes the norm of db_*-z less than every positive epsilon, hence zero in the original normed space. This replaces the former appeal to uniqueness of a metric limit with a direct distance calculation. All other arguments and all hypotheses are retained. I checked the trivial group, zero vector space, n=2, empty evaluation list and noncomplete coefficient cases again; the same finite-threshold and tail-bound arguments apply. No proof step exceeds 1000 characters or hides an additional independent lemma.

This repair changes the actual proof and its split-report record as well as documenting the requested comparison with the returned delivery. It does not set reviewed or promote side-project state; the fresh live-based delivery is for L to land after independent review. The final dry run and push follow these edits.
