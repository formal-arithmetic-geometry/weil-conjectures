# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-ultrametric-scalar-extension.json`: existing statement, split; statement unchanged; three assembly steps, 1539 characters of proof text.
- `dag/nodes/sec-six-functors-basics/lem-sfb-ultrametric-one-vector-extension.json`: new statement-only unsplit node; Mathlib verdict no match. Compact admissible balls and one-vector extension, old steps 2–4 (2273 characters of original proof).
- `dag/nodes/sec-six-functors-basics/lem-sfb-bounded-extension-zorn.json`: new statement-only unsplit node; Mathlib verdict no match. Chain upper bounds and conditional Zorn extension, old steps 5–6 (1453 characters of original proof).
- `citations.json`: all three step/node citations, copied verbatim from their statements.

## Attachments

None. Searched lean/WeilConjectures by the item id/docstring tag, proper_ultrametric, ultrametric extension, Hahn–Banach, bounded partial extension, and supSpanSingleton. No exact project declaration found. The existing Sheaf.Analysis.Normed.Module.ProperUltrametricScalarExtension declaration ContinuousLinearMap.exists_extension_of_proper_ultrametric explicitly has `sorry`; it is not an attachment. Its statement agrees with the item and its docstring contains the seven original steps. No Lean was changed or compiled.

## Wanted literature

WANTED: A. W. Ingleton, The Hahn-Banach theorem for non-Archimedean valued fields, scalar-valued extension theorem, for the item and lem-sfb-ultrametric-one-vector-extension. The blueprint paragraph (3) does not contain this functional-analysis proof. The existing agent-written proof remains the basis; neither a published proof nor a Stacks theorem for the whole extension assertion is claimed.

## What was wrong and how the return was repaired

The return requires actual distribution of work, not compression: the old seven-step proof had 4591 characters. The sandbox initially contained only dispatcher marker files, no delivered node, report or searches. I copied the current shared repository version, which includes the reviewed seven-step argument and its existing search/citation/provenance records, and preserved its statement, Lean record and review records. The two new nodes separate the compactness/local-extension argument from the purely algebraic chain/maximality argument; neither is a clause or renaming of continuous extension on V. The second makes the local extension hypothesis explicit instead of depending on the first node or the item. Their original proof workloads are 2273 and 1453 characters; both are substantial, not elementary two-line observations. Both new files have empty proof and proof_deps, null proof_origin, and status unsplit, for independent workers. The parent retains original steps 1 and 7 and uses their conclusions to assemble the two new results in step 2. No original argument was dropped: the complete text is preserved below and allocated to its new owner.

The inherited blueprint_refs ancestor command returns None because an older created.item chain terminates at a module name rather than a node. The parent retains its existing explicit det-thm-sf-ctf-stability-direct-images anchor. The first dry run rejected that anchor on the two new nodes because its computed nearest ancestor is None. I set their from.node to null, exactly as the ancestor command and preflight require, and kept the explicit det-thm-sf-ctf-stability-direct-images source location in from.place. Their via list is the parent's list with this item first. This records the broken inherited created.item chain honestly without changing ancestors, chapter or unit records or overriding a tool. The source document and exact argument locations remain explicit.

## Searches and source reading

The item retains the recorded original searches, read before deciding not to repeat its unchanged search question. For each new statement I ran the required msearch.py LeanFinder, Loogle, grep and LeanSearch searches, with a second semantic phrasing. Exact queries and actual summaries are in searches.jsonl and each new node's mathlib_searches. No unavailable service is represented as a negative result.

Read Mathlib/Analysis/Normed/Module/HahnBanach.lean:40–46 (IsRCLikeNormedField); Analysis/Convex/Cone/Extension.lean:160–164 (real scalars); Analysis/Normed/Operator/Extend.lean:17–23,51–56,89–91 (dense embedding); LinearAlgebra/Basis/VectorSpace.lean:289–296 (algebraic extension without a bound); LinearAlgebra/LinearPMap.lean:583–655 (chain suprema without boundedness/global-extension conclusion); Algebra/Module/Injective.lean:97–100,160–170,209–216,375–380 (Baer extensions with no norm bound). These are components or hypotheses of different theorems, not one-line specializations of either new node.

Read the current main-20261015 blueprint paragraph (3), the item's full seven-step proof and Lean docstring, the chapter and unit records, and the statements of def-weil-field, lem-trf-continuous-linear-map-norm-bound, lem-sfb-compact-closed-finite-intersection and lem-weil-pbc-zorn-lemma. Read Stacks topology.tex, Tag 005D, label lemma-intersection-closed-in-quasi-compact, including its finite-subcover proof. This is the compactness ingredient for the future local-extension worker, not a source for the full functional-extension statement. Read ContinuousLinearMap.bound at Operator/Basic.lean:132–133 and zorn_subset at Order/Zorn.lean:143–145. The agent source locations on the two new nodes identify exactly the old arguments to be proved; they do not claim the blueprint proves them.

Whole-DAG searches included one-vector, one-dimensional extension, bounded partial extension, admissible balls, chains/graphs, Ingleton, Hahn–Banach, and the relevant declaration names. Blueprint searches: ultrametric, bounded extension, linear functional, partial extension, Hahn, one-vector (no corresponding blueprint statement). Names of both new nodes were checked for absence. No existing statement gives these full obligations.

## Not duplicates

lem-sfb-ultrametric-one-vector-extension vs lem-sfb-proper-ultrametric-scalar-extension: the child is the explicit one-vector bounded construction for an already bounded g, including its admissible-ball witnesses; the parent extends a continuous f to all V and requires nontriviality.
lem-sfb-ultrametric-one-vector-extension vs lem-sfb-ultrametric-orthogonal-extension: the existing node adds an orthogonal vector to a finite orthogonal family over a finite l-adic extension and assumes a nearest point; the new node concerns arbitrary subspaces and scalar functional bounds over any field with compact scalar balls.
lem-sfb-ultrametric-one-vector-extension vs lem-sfb-norm-one-finite-subfield-projection: the existing node produces a norm-one retraction from an algebraic closure onto a finite l-adic subfield; this node treats one vector added to any subspace, not an algebraic closure or a retraction.
lem-sfb-ultrametric-one-vector-extension vs lem-sfb-compact-closed-finite-intersection: the existing leaf is the general compactness FIP principle; the new node proves the center/radius inequalities, FIP for this family, and the bounded linear extension formula. Its source has no shared Stacks tag since the full result is agent-written.
lem-sfb-bounded-extension-zorn vs lem-sfb-proper-ultrametric-scalar-extension: the new node assumes the local extension property as a hypothesis and proves the graph-chain/Zorn principle without compactness or continuity; it does not prove that local property, which is the analytic content of the item.
lem-sfb-bounded-extension-zorn vs lem-weil-pbc-zorn-lemma: the existing leaf assumes chain upper bounds for an arbitrary set family; the new node supplies them for bounded partial-linear-map graphs and identifies the maximal domain using its explicit local extension hypothesis.
lem-sfb-bounded-extension-zorn vs lem-sfb-countable-normed-orthogonal-basis: the existing node concerns countably spanned ultrametric spaces over finite l-adic fields and coordinates; the new node allows arbitrary-dimensional spaces and gives a conditional extension principle, with no basis/orthogonality conclusion.

## Review by Q139

I read the current item against its source and all three retained/replacement steps, rather than relying on the old pass. Its statement is unchanged, including the element t, exact metric topologies, arbitrary W, and absence of closedness/completeness. The source paragraph is only provenance for the arithmetic coefficient argument, not an Ingleton proof; the WANTED reference and agent origin remain explicit. The new nodes introduce every field, absolute value, vector space, norm, subspace and map, with inline meanings for norm, linearity, span, graphs, chains and maximality; their only external statement notion is the field definition. They contain statements only, with no hidden proof sketches or dependencies to the parent. No SGA source is used.

Parent step 1 takes C>0 and the norm inequality from lem-trf-continuous-linear-map-norm-bound: its statement explicitly allows arbitrary-dimensional incomplete normed spaces. The ultrametric triangle inequalities imply its ordinary ones by max(r,s)<=r+s; t gives its required nontrivial absolute value. Thus the exact hypotheses, including the induced subspace topology, hold.

Parent step 2 takes the one-vector map G with the same C from lem-sfb-ultrametric-one-vector-extension. This is stated for every bounded g on U and every x outside U, not merely the original f. Therefore it supplies precisely the universally quantified local condition of lem-sfb-bounded-extension-zorn; that node then states existence of a global h with the same bound and the required restriction. Its weaker ordinary triangle hypotheses follow from the same elementary max inequality. No use of either child's intended proof is made in this step. Parent step 3 uses only this explicit bound, linearity and C>0; the difference estimate and delta=epsilon/C are elementary and prove continuity in the exact given metrics. citations.json quotes the actual statements for all cited uses.

For the local child I checked arbitrary nonclosed and infinite-dimensional U: x outside U ensures every radius is strictly positive, but no positive uniform lower bound is assumed or needed. Center-distance control follows from the bound on g and the ultrametric inequality; the containment direction is smaller radius into larger. In B_0 every finite intersection contains the center of the least-radius ball among F union {0}, so the empty finite family is covered. The closedness calculation uses the ordinary scalar triangle inequality. Tag 005D applies to this genuinely compact subspace and a set-indexed closed family. For the formula I checked uniqueness of u+ax, the a=0 case, v=-a^{-1}u for a nonzero, and |a| C ||x-v|| = C ||u+ax||. The conclusion is bound-preserving, not norm-increasing. Trivially valued finite fields are allowed here: if the compactness hypotheses hold the same finite-intersection argument works, even though the parent needs t to obtain a bound from continuity.

For the Zorn child I checked that the graphs form a set inside P(V times K), that the graph of f belongs to it, and that a nonempty chain union is single-valued. Two vectors and their values occur in a common chain member, proving closure, additivity and the scalar rule; every pointwise bound comes from a member. The empty chain has graph(f) as an upper bound, which need not be the empty graph when W is nonzero. The exact set-family Zorn statement supplies a maximal graph. If its domain U is proper, the stated local condition provides G on U+Kx with a new pair over x, giving strict graph inclusion. These are the old steps 5–6, a substantive argument independent of compact scalar balls. W=V makes the local condition vacuous and h=f; W=0 and f=0 are valid, and V=0 is covered by W=V. Dense W needs no completeness argument; the parent construction still uses compact scalar balls and gives its bounded extension. Finite-dimensional examples over Q_p and the zero functional satisfy both extracted statements. No hypotheses have been added to the item.

The return's sole numbered obligation was to distribute all 4591 characters of work into at least two comparable new unsplit nodes and keep parent proof at most 3000 characters. The allocation below preserves the original arguments verbatim; the replacement parent has 1539 characters, no long non-elementary step, and exactly two new unsplit children. No statement dispute was found. B1–B9, C1–C7, D1–D5 and E1–E7 were checked by these concrete comparisons: the new nodes are substantial lemmas with their hypotheses explicit, not copies of the global continuous-extension conclusion, and the assembly cites exactly their statements. All remaining work is deliberately queued in those unsplit nodes, as requested.

## Original argument retained and allocated

### Old step 1 → parent step 1

The ultrametric inequalities imply the ordinary triangle inequalities because $\max(r,s)\leq r+s$ for $r,s\geq0$. Thus $K$, $V$, and the induced norm on $W$ satisfy the normed-space hypotheses of [lem-trf-continuous-linear-map-norm-bound]. The given $t$ makes the scalar absolute value nontrivial. Apply that node with source $W$ and target $K$ to obtain one fixed real $C>0$ such that $|f(w)|\leq C\|w\|$ for all $w\in W$. We will extend $f$ while preserving this bound.

### Old step 2 → lem-sfb-ultrametric-one-vector-extension

Consider any subspace $U$ containing $W$ and linear extension $g:U\to K$ with $|g(u)|\leq C\|u\|$, and fix $x\in V\setminus U$. For each $u\in U$ put $R_u=C\|x-u\|$ and $B_u=\{b\in K:|b-g(u)|\leq R_u\}$. For $u,v\in U$,
$$|g(u)-g(v)|\leq C\|u-v\|\leq\max(R_u,R_v).$$
Consequently if $R_u\leq R_v$ and $b\in B_u$, the scalar ultrametric inequality gives $|b-g(v)|\leq\max(R_u,|g(u)-g(v)|)\leq R_v$. Hence $B_u\subseteq B_v$. In particular the balls are totally ordered by inclusion and each contains its center. Each ball is closed: for $y\notin B_u$ set $\epsilon=(|y-g(u)|-R_u)/2>0$. If $|z-y|<\epsilon$ and $z\in B_u$, the ordinary triangle inequality gives $|y-g(u)|\leq |y-z|+R_u<\epsilon+R_u<|y-g(u)|$, a contradiction.

### Old step 3 → lem-sfb-ultrametric-one-vector-extension

Use $B_0=\{b:|b|\leq C\|x\|\}$ as a topological space with its subspace topology. It is nonempty and compact by the hypothesis on $K$. The subsets $B_0\cap B_u$ are closed in $B_0$ by the preceding calculation. For a finite set $F\subseteq U$, select an index $u_*$ of least radius among $F\cup\{0\}$; a least member exists in this nonempty finite set of real radii. Then $B_{u_*}\subseteq B_0\cap\bigcap_{u\in F}B_u$, and its center belongs to that intersection. This also deals with $F=\varnothing$. Apply [lem-sfb-compact-closed-finite-intersection] to the compact space $B_0$ and the set-indexed closed family $(B_0\cap B_u)_{u\in U}$. Obtain $b\in\bigcap_{u\in U}B_u$. This is the compactness step (Stacks Tag 005D, lemma-intersection-closed-in-quasi-compact); no lower bound for the radii or completeness of $U$ is needed.

### Old step 4 → lem-sfb-ultrametric-one-vector-extension

Every element of $U+Kx$ has a unique expression $u+ax$ with $u\in U$ and $a\in K$: two expressions with different coefficients would imply $x\in U$ by dividing their difference by the nonzero coefficient. Define $G(u+ax)=g(u)+ab$. This formula is additive and scalar-preserving by adding and scaling the unique expressions, and for $a=0$ it equals $g(u)$ and has the required bound. If $a\ne0$, put $v=-a^{-1}u\in U$. Since $b\in B_v$, linearity and norm homogeneity give
$$|G(u+ax)|=|a|\,|b-g(v)|\leq |a|C\|x-v\|=C\|u+ax\|.$$
Thus the explicitly constructed proper extension on $U+Kx$ preserves the same constant $C$. The uses of minus signs here follow from $|-1|=1$, which follows from multiplicativity and $(-1)^2=1$.

### Old step 5 → lem-sfb-bounded-extension-zorn

Let $\mathcal S$ be the set of subsets of $V\times K$ that are graphs of linear maps $g:U\to K$, for subspaces $W\subseteq U\subseteq V$, restricting to $f$ on $W$ and satisfying $|g(u)|\leq C\|u\|$. This is a set, being a subfamily of the power set of $V\times K$, and it contains the graph of $f$. For a nonempty chain of such graphs, take their union. Comparability ensures a unique value at each vector in the union of the domains. Two vectors in that domain lie together in one chain member, so their sum and scalar multiples satisfy the same linear identities there. Thus the union is again the graph of a linear map on a subspace containing $W$; it agrees with $f$, and every value satisfies the same bound because it comes from one member. This union is an upper bound in $\mathcal S$. For the empty chain the graph of $f$ is an upper bound.

### Old step 6 → lem-sfb-bounded-extension-zorn

Apply [lem-weil-pbc-zorn-lemma] with underlying set $V\times K$ and family $\mathcal S$, using the upper bounds just constructed, including the empty-chain case. Let the maximal graph be that of $g:U\to K$. If $U\ne V$, choose $x\in V\setminus U$ and repeat the ball construction and the explicit formula of steps 2–4 for this $U,g,x$. Step 3 uses [lem-sfb-compact-closed-finite-intersection] and supplies $b$; step 4 supplies a bounded extension to $U+Kx$. Its graph strictly contains the maximal graph, since its domain additionally contains $x$, a contradiction. Therefore $U=V$. Put $\widetilde f=g$.

### Old step 7 → parent step 3

The maximal graph already ensures $K$-linearity and $\widetilde f|_W=f$. For every $v,w\in V$, linearity and its bound give
$$|\widetilde f(v)-\widetilde f(w)|\leq C\|v-w\|.$$
For any $\epsilon>0$, take $\delta=\epsilon/C>0$; then $\|v-w\|<\delta$ implies $|\widetilde f(v)-\widetilde f(w)|<\epsilon$. Hence $\widetilde f$ is continuous for exactly the prescribed metrics, proving every clause.

## Unfinished work

No repair obligation remains open. The two new statements are intentionally unsplit; their proofs are the independently assignable work requested by the return. Delivery validation and push results follow below.

## Delivery validation

First dry run: two B9 ancestry diagnostics only, repaired by recording the computed null ancestor on the new nodes and retaining the known blueprint location in from.place. No mathematical change resulted.

Final dry run exited 0: OK (not pushed), preflight passed at 2b48edac3cd. The required server preflight, DAG and split review gates passed. Parent statement unchanged; two new unsplit nodes, zero Mathlib leaves.


## Landing-return repair on 2026-10-22

The latest return is distinct from the earlier re-split order: the reader approved the split, but landing reported that the side completion had not been promoted into the live DAG read by the queue. I retained the delivered sandbox, both extracted statements, the full original argument allocation, citations and all recorded Mathlib searches. I compared the retained item with the current shared DAG record: exactly proof, proof_deps and split_report differed. In particular statement, stmt_deps, blueprint provenance, Lean and review/audit records agreed. The shared record still has the seven-step proof and the released stage-1 re-split order, while neither child id exists there. I rebuilt the sandbox item from that current record and overlaid the retained three-step split, then added this repair to split_report. Thus this delivery explicitly carries the re-split on the current DAG without overwriting unrelated current fields.

I re-read the current statements of def-weil-field, lem-trf-continuous-linear-map-norm-bound, lem-sfb-compact-closed-finite-intersection and lem-weil-pbc-zorn-lemma, and both retained children. The current norm-bound statement is byte-for-byte the retained citation quotation; the two child statement quotations also still match exactly. Step 1 still has the nontrivial scalar supplied by t and the induced norm on W, so the bound applies without completeness. Step 2 still supplies the same C for every U,g,x required by the Zorn child's local condition; neither child depends on the parent. Step 3 is the explicit epsilon/C estimate. I checked citation coverage for all three cited step/node pairs against these actual statements. No cited statement needs a mathematical adjustment after rebasing.

I also reopened the current blueprint paragraph (3), chapter/unit records, the project's existing Lean theorem with its sorry, Mathlib ContinuousLinearMap.bound, and Stacks topology.tex lemma-intersection-closed-in-quasi-compact (Tag 005D). The source does not acquire an Ingleton proof by this rebase, so the original agent provenance and WANTED entry remain. Current whole-DAG and blueprint searches disclose no replacement for either extracted statement; blueprint_refs still computes None for the inherited broken created.item chain, as in the accepted retained delivery. Small cases W=V, V=0, zero f, and the empty chain/intersection still satisfy the unchanged statements. The parent's 1539-character assembly has no non-elementary step over 2000 characters. The required two new unsplit arguments remain separate, preserving the earlier re-split obligation as well as addressing this landing return. The live promotion itself is the maintainer's landing operation, not a worker edit to coordination files.

The initial required repair dry run exited 0 at da7c97f45a6 (OK, not pushed). After the explicit current-record refresh and this report update, a fresh final dry run and delivery are required; the earlier receipt is historical only.
