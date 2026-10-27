## Worker report

Files written, all under the Q91 item sandbox:
- dag/nodes/sec-six-functors-basics/lem-sfb-norm-one-finite-subfield-projection.json: repaired split, unchanged statement, four assembly steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-admissible-scalar-balls.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-contractive-extension-from-admissible-values.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim cited statements for each use, numbered by the repaired proof steps.

Attachments: none. I searched WeilConjectures by blueprint id and by norm-one/contractive functional notions; no declaration states the item. The recorded Sheaf.NumberTheory.Padics.NormOneFiniteSubfieldProjection theorem Padic.exists_normOne_finiteSubfield_projection is still sorry (read the whole file), so it is not a finished attachment. No Lean was written or compiled.

WANTED: A. W. Ingleton, The Hahn-Banach theorem for non-Archimedean valued fields, scalar-valued extension theorem, for the item and both new nodes. It is not supplied by the local blueprint. The proofs below are agent arguments, not attributed to an unread source. The compact finite-intersection ingredient is Stacks Tag 005D, topology.tex, lemma-intersection-closed-in-quasi-compact, read in full; it already has the node lem-sfb-compact-closed-finite-intersection. The Zorn ingredient already has lem-weil-pbc-zorn-lemma. No SGA route is used.

Repair baseline: despite the brief's retained-sandbox expectation, there were no node files or report in this sandbox. The mandatory initial dry run exited with “FAILED: no node files under .../dag/nodes/”. I copied the current read-only repository item, whose seven-step proof and reviewer fix retain the 4565-character argument identified in the return. Its statement, previous searches, reviewed metadata and Lean record are preserved. No repository or launcher file was edited, and no git command was run there. During local review I also corrected two literal newline escapes in the first new statement to real line breaks and refreshed its verbatim citation. The current item statement is correct; no statement dispute is raised. Nothing is abandoned or left blocked.

## Repair of every returned point

The return requires at least two separate, comparable statement-only tasks and an assembly proof of at most 3000 characters. Old steps 2-3 (1382 characters) become lem-sfb-admissible-scalar-balls. Old steps 4-6 (2075 characters) become lem-sfb-contractive-extension-from-admissible-values. Old step 1 (restriction norm, compactness and vector norm axioms) and step 7 (identity, Lipschitz continuity and norm one) stay in the item. These two chunks have different hypotheses and conclusions and can be proved independently: the second ASSUMES the scalar-value condition and does not use the first as a proof dependency. It contains no compactness argument; the first contains no global extension or Zorn conclusion. Their combination genuinely separates the original analytic and maximal-extension arguments, rather than putting the whole target into one child. The unchanged target is recovered by taking W=F and the identity functional.

The new files have proof=[], proof_deps=[], proof_origin=null and status=unsplit. All proof details are in this report, with the original seven steps reproduced verbatim below to make the preservation auditable. Both statements explicitly introduce K, V, the absolute value, ultrametric norm, domains, maps and quantifiers. No proof sketch is embedded in either statement.

## Arguments assigned to the two new tasks

For lem-sfb-admissible-scalar-balls, use the original steps 2-3 with K,V in place of F,Omega and without the unnecessary condition U contains F or g fixes F. For R_u=||x-u||, contractivity gives |g(u)-g(v)| <= ||u-v|| <= max(R_u,R_v). Therefore the balls B_u centered at g(u), radius R_u, are nested in increasing radius. The original epsilon argument proves they are closed; each contains its center. B_0 is compact by the new node's hypothesis and nonempty since it contains zero. For each finite family of constraints adjoin index 0 and choose one of minimal radius. Its center belongs to all these balls, including B_0; for an empty family this is still valid. Apply the exact statement of lem-sfb-compact-closed-finite-intersection on the subspace B_0 to the closed subsets B_0 intersect B_u. This yields b satisfying all constraints. Nothing requires U to be closed, finite dimensional or complete. This is the entire compactness subargument of old steps 2-3, not simply a quoted spherical-completeness theorem.

For lem-sfb-contractive-extension-from-admissible-values, fix W and f as in its statement. For any contractive partial extension g on U containing W and any x outside U, use the ASSUMED scalar-value condition for this U,g,x to select b. In U+Kx every vector has a unique expression u+ax (a difference with nonzero scalar coefficient would place x in U). Define G(u+ax)=g(u)+ab. This is linear and restricts to g. At a=0 its bound is that of g; for a nonzero put v=-a^{-1}u. Then G(u+ax)=a(b-g(v)), u+ax=a(x-v), hence |G(u+ax)| <= |a| ||x-v|| = ||u+ax||. This is the full old step 4, including its signs and the zero scalar case. The identity |-1|=1 follows from multiplicativity and |-1|^2=1.

Now order by inclusion the set of graphs of all contractive partial linear extensions of the given f. They are subsets of V times K, and the graph of f is a member. For a nonempty chain, its union is single-valued by comparability and has the union of the domains as its domain. Two vectors lie together in one member, so addition and the additive map equation hold there; scalar closure and homogeneity hold in the member containing a vector. Agreement with f and the bound hold pointwise. Thus this union graph is an upper bound in the same set. The empty chain is bounded by the graph of f. Apply exactly lem-weil-pbc-zorn-lemma, with X=V times K, to get a maximal graph. If its domain U is proper, the preceding G strictly enlarges it, including a pair with first coordinate x outside U. This contradicts maximality and proves the domain is all V. This preserves all old steps 5-6, with f replacing the identity start. The eventual worker can use LinearPMap machinery, but must establish the bound-preserving statements rather than cite real Hahn-Banach.

## Not duplicates

lem-sfb-admissible-scalar-balls vs lem-sfb-compact-closed-finite-intersection: the existing Tag 005D leaf assumes a closed family already has the finite intersection property in a compact space; the new statement constructs and checks the admissible functional balls and their FIP from norm inequalities. It is an application of this existing node, not its restatement; Tag 005D is not falsely attributed as the source of the entire analytic statement.
lem-sfb-admissible-scalar-balls vs lem-sfb-proper-ultrametric-scalar-extension: the existing node concludes existence of a continuous global extension with no sharp bound, and states no common scalar-value assertion for a prescribed contractive g and external x. Its proof, which contains a related argument, is not its statement and cannot be cited as this result.
lem-sfb-contractive-extension-from-admissible-values vs lem-sfb-proper-ultrametric-scalar-extension: the existing node assumes compact scalar balls and a continuous initial functional and concludes only continuity of an extension. The new task assumes solvability of the explicit scalar-value constraints instead of compactness or a nontrivial valuation, and concludes the pointwise contractive bound. The existing statement gives neither the bound nor the conditional generality.
lem-sfb-contractive-extension-from-admissible-values vs lem-weil-pbc-zorn-lemma: Zorn supplies a maximal set element given chain upper bounds; it supplies no partial linear graphs, no one-dimensional enlargement formula and no norm preservation. The new statement's substantial work is exactly constructing these and deriving totality.
lem-sfb-admissible-scalar-balls vs lem-sfb-ultrametric-orthogonal-extension: orthogonal extension assumes a finite orthogonal basis and an attained best approximation, and gives another orthogonal vector; it says nothing about an arbitrary partial scalar functional or infinitely many admissible balls.
lem-sfb-contractive-extension-from-admissible-values vs lem-sfb-dense-subspace-contractive-extension: the existing leaf requires a dense initial subspace and a complete target; the new task requires neither and uses an explicit all-partial-maps scalar-value hypothesis instead.
lem-sfb-contractive-extension-from-admissible-values vs lem-sfb-finite-subfield-continuous-linear-retraction: that node is restricted to finite p-adic coefficient subfields and gives no norm bound; the conditional extension task has arbitrary W,V and no field-extension or algebraicity assumption.

Before choosing the ids I searched all DAG files by contractive, Hahn-Banach, partial functional/graph, admissible balls, spherical completeness and the two candidate ids, and read the relevant existing node statements. Blueprint searches for contractive/Hahn/one-dimensional/partial linear/norm-one/spherical, bounded linear, ultrametric, Hahn, partial functional, admissible scalar and contractive extension yielded no corresponding blueprint statements. tools/blueprint_refs.py ancestor prints None for this item's old created.item chain, which terminates at the module string Sheaf.SixFunctors.CtfStabilityDirectImages rather than an imported node. The first full dry run rejected the children's nonnull from.node because the mechanical ancestor is None. I repaired both new nodes to use from.node=null, exactly the command's result and the schema's supported representation; their from.place still explicitly names det-thm-sf-ctf-stability-direct-images and paragraph (3), with the item prepended to the retained via list. The existing item's reviewer-corrected explicit provenance remains unchanged. I did not change created fields, add false blueprint markers, or modify the checker. No new blueprint claim is invented. The unit record is inherited from the old import (sec-six-functors); I read it and the current sec-six-functors-basics chapter and the paragraph (3) source, and made no route or unit changes.

## Review by Q91

I read the complete paragraph (3) of the main-20261015 direct-images proof, the current item, its two norm/properness dependencies, and its two old compactness/Zorn dependencies. The blueprint motivates the arithmetic projection input but does not prove it; both new statements are correctly labelled agent-formulated auxiliaries at this precise place, with Ingleton WANTED. I also read Stacks topology.tex Tag 005D and the Mathlib source of the tempting extension candidates. HahnBanach.lean lines 40-46 requires IsRCLikeNormedField; Basis/VectorSpace.lean lines 289-296 has no metric bound; Convex/Cone/Extension.lean lines 53,65,113,160 is over real scalars. None is a one-line specialization of either new node. Every query was run with msearch.py and its actual log record is copied exactly; the rate-limited LeanSearch request is unavailable, and the later successful differently phrased request is recorded separately.

Step 1 cites lem-weil-l-adic-extension-absolute-value for uniqueness, verified for finite F/Q_l and the restriction of Omega's extending absolute value, then lem-weil-l-adic-extension-proper for compact closed balls with that identified norm. This preserves the maintainer's earlier C4 fix. Multiplicativity and the ambient ultrametric inequality give exactly the vector-norm axioms of both new statements.

Step 2 cites only lem-sfb-admissible-scalar-balls. I verified that its statement quantifies over every U and every contractive g, without requiring U to contain F, and gives precisely |b-g(u)| <= ||x-u||. This is the ALL-partial-maps scalar-value condition used in step 3, not merely existence for the identity start. Its compactness hypothesis is exactly what step 1 established, and its norm topology is the same restricted topology.

Step 3 cites only lem-sfb-contractive-extension-from-admissible-values. Its statement explicitly accepts the condition from step 2, accepts W=F and the identity, and concludes an F-linear total extension agreeing on W with pointwise bound one. In the field Omega, scalar multiplication by F is inherited multiplication, so W=F is an actual F-subspace and the norms agree on it. I checked |id(a)|=||a||, including a=0. No dimension, completeness, algebraic basis, or spherical-completeness hypothesis is silently supplied here.

Step 4 retains the calculation of original step 7, replacing its obsolete reference to the old graph set with the conclusion of step 3: subtraction and the established bound give the 1-Lipschitz inequality; delta=epsilon proves continuity, and p_F(1)=1 gives the norm-one equality. This is elementary from the constructed map and requires no new analytic theorem. The item statement remains byte-for-byte identical to the baseline. Every citation in steps 1-3 has its full statement copied verbatim into citations.json, so the review does not rely on facts in cited proofs.

For the new scalar-ball statement I checked U={0}, x nonzero (b=0 is feasible); zero-radius balls; empty finite families (adjoin 0); repeated/equal radii (nesting still holds); U=V (external-vector condition vacuous); and infinite or nonclosed U. For the conditional-extension statement I checked W={0}, f=0; W=V (take f itself); V=0; trivial scalar absolute value; the empty chain; nonempty chains without a largest member; scalar a=0; and the sign v=-a^{-1}u. Compactness and nontriviality of K are deliberately absent from the second statement because it assumes the exact condition that the compact-ball argument provides. Both statements are true in these edge cases.

Against B-E: two self-contained statement-only nodes, explicit norm/topology notions and field-definition dependency, TeX escaped once, precise source provenance with no false Stacks attribution, logged searches and candid unavailable verdict, no closed attachment, no circular dependency, and no clause merely moved intact to one child. The report preserves the detailed subarguments as required by the return. The repaired item has no step over 2000 characters and total proof text is below 3000; the long former graph and compactness arguments now have their own tasks. The only removed direct proof dependencies are compact FIP and Zorn, whose roles are explicitly assigned to the new nodes above, not discarded. The original restriction-norm/properness references remain direct. No external messages, Lean builds, or unauthorized file writes were made.

## Repair of the promotion return (2026-10-22)

The latest return says the reader approved the delivery, but landing refused it because the side completion had not been promoted into the live DAG. I retained the two statement-only nodes, their recorded searches, the full original proof audit and all existing citations. The mandatory first dry run in this repair exited successfully: OK (not pushed) at 92172cd6a9d. The delivery script constructs this commit on current origin/sheaf-dag; no git command was run in the shared read clone.

I compared every retained node with the current shared DAG. Neither auxiliary exists there. For the item, only proof, proof_deps and split_report differ: statement, statement dependencies, source, blueprint provenance, searches and maintainer metadata agree. I re-read all external cited statements: the uniqueness theorem identifies the restricted finite-field norm, and properness then applies to that very norm. Neither statement has changed relative to the verbatim citations. I also re-read both retained auxiliary statements against steps 2 and 3: the first gives all partial-map scalar-value constraints, and the second accepts those exact constraints and returns the required contractive extension. All four citations remain verbatim. The field-definition dependency still defines a commutative field, and the compact-FIP and Zorn ingredients retained in the report still have exactly the required hypotheses, including the empty family/chain.

As a concrete repair beyond rebasing, I corrected step 4's reference to the formerly defined set of partial graphs: that set now belongs only to the auxiliary's argument, so the assembly now takes linearity, the retraction identity and the bound directly from step 3. The subsequent Lipschitz and norm-one calculations are unchanged. The full original step remains preserved verbatim in the historical audit below. I refreshed the split report and this repair review, with no statement changes or new searches. The current upstream declaration search gives no attachment, and the Sheaf declaration still ends in sorry. The two independent unsplit tasks, edge-case checks and source/WANTED findings remain valid. A fresh final dry run and push follow this update.

## Original proof retained verbatim for repair audit

### Original step 1

Give $F$ the restriction of the specified absolute value on $\Omega$. It extends the $\ell$-adic absolute value, and $F/\mathbf Q_\ell$ is finite-dimensional by hypothesis, so by the uniqueness in [lem-weil-l-adic-extension-absolute-value] it is the extending absolute value $|\cdot|_F$ of $F$. Apply [lem-weil-l-adic-extension-proper] with $E=F$: every closed ball $\{b\in F:|b-a|\leq r\}$, $r\geq0$, is compact. We regard $\Omega$ as an $F$-vector space with norm $\|x\|=|x|$. Multiplicativity gives $\|ax\|=|a|\|x\|$, and its given nonarchimedean inequality gives $\|x+y\|\leq\max(\|x\|,\|y\|)$. The identity on the subspace $F\subseteq\Omega$ satisfies the bound $|a|\leq\|a\|$.

Cited nodes: lem-weil-l-adic-extension-absolute-value, lem-weil-l-adic-extension-proper

### Original step 2

For any $F$-subspace $U\subseteq\Omega$ containing $F$, any $F$-linear $g:U\to F$ restricting to the identity on $F$ with $|g(u)|\leq\|u\|$, and any $x\in\Omega\setminus U$, put $R_u=\|x-u\|$ and $B_u=\{b\in F:|b-g(u)|\leq R_u\}$ for $u\in U$. Linearity and the bound imply
$$|g(u)-g(v)|\leq\|u-v\|\leq\max(R_u,R_v).$$
If $R_u\leq R_v$ and $b\in B_u$, then $|b-g(v)|\leq\max(|b-g(u)|,|g(u)-g(v)|)\leq R_v$; hence $B_u\subseteq B_v$. Each ball contains its center. It is closed: if $y\notin B_u$, take $\epsilon=(|y-g(u)|-R_u)/2>0$; $|z-y|<\epsilon$ and $z\in B_u$ would give $|y-g(u)|\leq|y-z|+R_u<\epsilon+R_u<|y-g(u)|$. The ordinary triangle inequality used here follows from $\max(r,s)\leq r+s$ for nonnegative $r,s$.

Cited nodes: none (elementary)

### Original step 3

The ball $B_0=\{b\in F:|b|\leq\|x\|\}$ is compact by step 1 and contains zero. For every finite subset $A\subseteq U$, select $u_*$ of least radius among $A\cup\{0\}$. The containment calculation of step 2 shows that $g(u_*)$ belongs to $B_0\cap\bigcap_{u\in A}B_u$. This also proves nonemptiness when $A=\varnothing$. Thus the closed subsets $B_0\cap B_u$ of the compact topological space $B_0$ have the finite intersection property. Apply [lem-sfb-compact-closed-finite-intersection] with index set $U$ to obtain $b\in F$ satisfying $|b-g(u)|\leq\|x-u\|$ for every $u\in U$. All compactness is in $F$; no compactness or completeness of $\Omega$ or $U$ is used.

Cited nodes: lem-sfb-compact-closed-finite-intersection

### Original step 4

Every element of $U+Fx$ has a unique expression $u+ax$ with $u\in U$ and $a\in F$: a difference of two expressions with distinct coefficients would imply $x\in U$. Define $G(u+ax)=g(u)+ab$. Adding and scaling the unique expressions proves $F$-linearity; at $a=0$ the formula equals $g(u)$, so $G$ extends $g$ and fixes $F$. If $a\ne0$, let $v=-a^{-1}u\in U$. The inequality for $b$ yields
$$|G(u+ax)|=|a|\,|b-g(v)|\leq |a|\|x-v\|=\|u+ax\|.$$
For $a=0$ use the original bound on $g$. Thus $G$ is a contractive extension to a strictly larger subspace. The sign identities used here follow from $|-1|=1$, since $|-1|^2=1$. Steps 2–4 establish this extension construction for every such $U,g,x$.

Cited nodes: none (elementary)

### Original step 5

Let $\mathcal S$ be the set of graphs in $\Omega\times F$ of all $F$-linear maps $g:U\to F$ with $F\subseteq U\subseteq\Omega$, $g|_F=\mathrm{id}_F$, and $|g(u)|\leq\|u\|$. This is a set of subsets of $\Omega\times F$, and the identity graph on $F$ belongs to it. For a nonempty inclusion-chain of these graphs take the union. Comparability makes the union single-valued; its domain is the union of the subspaces. Any two domain vectors belong together to one chain member, which verifies closure under addition and the linear identity there; scalar multiplication is verified in the member containing the vector. Thus the union is again a linear graph. It contains $F$, fixes $F$, and satisfies the same pointwise bound, each value being a value in a chain member. Hence it is an upper bound in $\mathcal S$. For the empty chain use the identity graph on $F$.

Cited nodes: none (elementary)

### Original step 6

Apply [lem-weil-pbc-zorn-lemma] to $X=\Omega\times F$ and the set $\mathcal S$, using the upper bounds of step 5, including the empty chain. Obtain a maximal graph, of a map $g:U\to F$. If $U\ne\Omega$, choose $x\in\Omega\setminus U$. Steps 2–4, with this $U,g,x$, construct a contractive linear map $G:U+Fx\to F$ fixing $F$. Its graph belongs to $\mathcal S$ and strictly contains the graph of $g$, since it also contains a pair with first coordinate $x$. This contradicts maximality. Therefore $U=\Omega$, and set $p_F=g$.

Cited nodes: lem-weil-pbc-zorn-lemma

### Original step 7

The defining conditions of $\mathcal S$ give $F$-linearity, $p_F(a)=a$ for every $a\in F$, and $|p_F(x)|\leq|x|$ for every $x\in\Omega$. For $x,y\in\Omega$,
$$|p_F(x)-p_F(y)|=|p_F(x-y)|\leq|x-y|.$$
Given $\epsilon>0$, choose $\delta=\epsilon$ in this inequality to obtain continuity for the specified norm topologies. At $x=1$ equality holds in the bound, so the map indeed has norm one. The argument never completes $\Omega$.

Cited nodes: none (elementary)
