# Q136 repair: lem-sfb-ordered-join-partial-contraction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ordered-join-partial-contraction.json`: existing statement unchanged; four-step assembly, 2139 characters (after the fresh landing-return clarification).
- `lem-sfb-ordered-join-single-color-identities.json`: new statement, unsplit; no Mathlib match. Own task: cancellation for two deletions and signed insertion in the missing/present-color cases (old calculations 1-4).
- `lem-sfb-ordered-join-prefix-telescope.json`: new statement, unsplit; no Mathlib match. Own task: graded algebra of ordered prefixes and annihilation on generating proper-support subgroups (old calculations 5-6, generalized).
- `lem-sfb-ordered-join-functorial-expansion.json`: new statement, unsplit; no Mathlib match. Own task: operator naturality and the unreduced powerset expansion (old calculations 7-8).
- `citations.json`: one verbatim statement quote for every citation of every assembly step.

## Attachments

None. I searched `lean/WeilConjectures/` by the blueprint id and the ordered-join, color-insertion and operator notions. No matching declaration was found. `lean/Sheaf/AlgebraicTopology/OrderedJoinPartialContraction.lean:213` states the complete item, but its proof is `sorry` at line 227, so it is not an attachment. Its definitions and docstring were read, not modified or compiled.

## WANTED

None. The source of this calculation is explicitly an agent-written expansion. There is no claim that the blueprint proves the combinatorial statements, and no SGA source is used.

## Returned issue and repair

The human requested at least two comparable independent statement-only tasks and a parent proof of at most 3000 characters. I created three; their assigned original argument sizes are 2215, 1154, 1854 characters, respectively (the first includes basis extension, also retained as the parent's elementary setup). Each has self-contained hypotheses, source and blueprint place, empty proof and proof_deps, null proof_origin, and status unsplit. None refers to the parent for its mathematical meaning or assumes its conclusion. The middle task is a general lemma for arbitrary graded abelian groups, not a restatement of contraction of the join. The last proves identities for individual operators and individual summands, leaving naturality and the coefficient list for their sum to the parent. The full original argument is preserved below; it was not shortened or blurred to meet the limit.

The sandbox initially contained only dispatcher marker files, no saved JSON, report or searches.jsonl. I continued from the exact eight-step proof currently in the shared repository, whose 5223-character text matches the returned description. All existing metadata, statement, citations and Mathlib searches in that node are retained. The delivery tool rebases owned split fields onto current server state.

## What remains

The three new statements intentionally await proofs by other workers. No Lean was written and no compiler, Lake or local DAG/preflight checker was run. The only changes are sandbox files; server checks and packaging use the authorized delivery command.

## Not duplicates

lem-sfb-ordered-join-single-color-identities vs lem-sfb-ordered-join-partial-contraction: the new node isolates local identities for every color and every degree; it states neither the global S homotopy nor naturality/expansion.
lem-sfb-ordered-join-prefix-telescope vs lem-sfb-ordered-join-partial-contraction: the new lemma assumes the local homotopy identities on arbitrary graded abelian groups and derives a product defect and proper-support annihilation, without constructing any ordered join.
lem-sfb-ordered-join-functorial-expansion vs lem-sfb-ordered-join-partial-contraction: the new node concerns each c_i, R_i and P_i c_i, with no boundary or contraction identity; the parent composes and adds these results.
lem-sfb-ordered-join-single-color-identities vs lem-sfb-poset-augmented-chain-prism: the latter is a finite-poset prism for comparable monotone maps, whereas arbitrary possibly infinite sets with distinct colors and a missing/present-color operator are needed here.
lem-sfb-ordered-join-single-color-identities vs lem-coef-extra-degeneracy-contraction: that node requires a full simplicial extra degeneracy and concludes a simplicial homotopy; our colorwise operator is zero on symbols containing its color.
lem-sfb-ordered-join-functorial-expansion vs def-coef-ordered-join: that is the definition of a simplicial-set join, not a theorem about signed integer-chain replacements or an unreduced coefficient recipe.
lem-sfb-ordered-join-prefix-telescope vs lem-kun-functor-preserves-hocolim: that is a countable coproduct telescope triangle preserved by an exact functor; it says nothing about finite ordered homotopies or support-annihilating products.
lem-sfb-ordered-join-functorial-expansion vs def-weil-pbc-simplicial-ordinal-path: that defines a doubled-ordinal simplicial path object, not arbitrary-color pointed-set operators or their subset expansion.

I searched the whole DAG for ordered joins, color insertion, replacement homotopies, remainder prefixes and telescoping; I read the candidate statements above. Blueprint searches for ordered join, colored, insertion, telescop, replacement and contraction yielded no equivalent imported statement. Unrelated hits concern ring contractions, triangulated telescope triangles, coefficient definitions and generic sheaf replacements. The ancestor tool returns None because of the existing chain ending at a module item; this inherited circumstance was already accepted on the item. New via chains add the item before its retained chain.

## Mathlib searches and source comparison

`search-plan.json`, `search-results.json` and the actual msearch-produced `searches.jsonl` retain the searches and answers. Every new node has two distinct LeanFinder phrasings, Loogle, grep and an attempted LeanSearch. LeanSearch rate-limited the prefix and expansion queries; those records explicitly say unavailable. LeanFinder, Loogle and grep ran for all three nodes. Additional logged greps locate candidates; source excerpts were read.

For the single-color task, `AlgebraicTopology.AlternatingFaceMapComplex.d_squared` at Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean:74 assumes a simplicial object and proves only its boundary relation. Our groups are defined on distinct-color faces, with augmentation, and the single-color identity is additional. `DoldKan.homotopyPToId` at AlgebraicTopology/DoldKan/HomotopyEquivalence.lean:35 concerns Dold-Kan projection P, not our chosen-point replacement. Bar resolutions require group tuples. Alternating-map insertion identities are about multilinear alternating maps, not these free chains.

For the prefix task, Homotopy constructors/addition/composition can help a later proof, but they do not state the finite prefix formula with its specified order and the generating-subgroup annihilation clause. In particular a one-line application does not prove the missing-color product assertion. No searched statement covers the task.

For the expansion task, `Finset.prod_sub` at Algebra/BigOperators/Ring/Finset.lean:259 and `prod_sub_ordered` at line 264 assume a commutative ring. Endomorphisms under composition are not a commutative ring, and identifying the restricted replacement actions with a commutative algebra would itself require proof. Those lemmas do not state naturality of c_i/R_i, missing-color vanishing, or the unreduced symbol list. Generic simplicial splittings and simplex-category normal forms concern different objects. These are candidates for ingredients, not matches for the node.

## Review by Q136

I read the current main-20261015 direct-images proof, paragraph (3), the chapter and unit records, the entire returned eight-step calculation, and the corresponding Lean definitions and theorem docstring. The blueprint paragraph constructs direct image through open/proper factors; it contains no ordered-join lemma. For each new node its source place therefore explicitly labels the relevant calculations as an agent expansion; the prefix node labels its generalization. The route through arithmetic continuous-cocycle descent is unchanged. For the basis notion I opened def-weil-pbc-free-module and its Stacks algebra.tex item-free-module (00C2 under 00AQ), and checked that its statement specifies finite unique basis expansion.

Assembly step 1 uses exactly that unique finite expansion for linear extension and equality on basis symbols. Step 2 cites the entire conclusion of the single-color node: both d squared and d c_i+c_i d=1-R_i, with every q, including -1 and r-1. I checked that its increasing-color positions and signs agree with the existing definitions, and that it does not assume d squared in order to prove d squared.

Assembly step 3 uses the prefix node's stated commutation/telescoping identity and its stated generating-subgroup annihilation criterion, not its future proof. The hypotheses are verified explicitly: A_q=J_q, and step 2 supplies both algebraic identities. In each required degree the color sets have size q+1<r. The integer spans of fixed-color basis symbols generate J_q; each two-term R_i formula stays in that span, or is zero when i is missing. The degree shifts in H_q use P_{i,q+1}, so H equals S with the original rightmost-first composition. The zero-domain fact gives S_-2=0. The new lemma does not require pairwise commutation or unique subgroup decomposition.

Assembly step 4 uses the expansion node's two naturality identities and its exact individual-summand formula. I checked that a vertex map preserves colors even when noninjective, and w_i is exactly u_i(v_i). Successive substitution through a fixed finite composite and addition gives naturality for S. Concatenation of the subset lists keeps repeated symbols uncollected, so it never requires deciding equality of vertices. This proves the original list assertion, and on the empty symbol only the color-zero summand remains. The citations file copies these actual statements verbatim.

For delivery-errors B I checked independent self-contained statements, explicit degree conventions, specified bases, source honesty, TeX escapes, empty unsplit proof fields and the real search log. For C I opened every cited statement and checked all facts used are present; only basis linearity and final finite composition/addition remain elementary. For D I verified no node moves the whole item or creates a cycle: the first and third only cite the existing free-module definition, and the abstract middle one needs no parent. The three proof tasks are independently startable, as the human requested. For E I checked r=1, empty faces, singleton colors, top degree, missing early colors, vertices already equal to chosen points, and noninjective maps. The paired deletion signs and present/missing-color insertion cases remain exactly as in the old proof; no extra hypothesis or statement correction was needed. Edge computations and their result are recorded after running the sandbox verifier.

There is no parent step longer than 2000 characters. All 5223 characters of old proof are reproduced below, assigned to the separate tasks; its argument is retained for future workers without putting a proof sketch into any unsplit node's statement.

## Work allocation and preserved original argument

Task 1 receives calculations 1-4, task 2 receives calculations 5-6 (with the abstract subgroup formulation replacing fixed-color spans), and task 3 receives calculations 7-8. The parent's basis setup and empty-face observation remain explicit assembly checks. Every argument of the returned version is present verbatim here:

### Original calculation 1

All maps are defined first on the specified bases, then extended by finite integer linear combination. This gives well-defined homomorphisms: for $d$ there are $q+1$ terms, for $c_i$ at most one, and for $R_i$ at most two. By [def-weil-pbc-free-module], uniqueness of the finite basis expansion shows that two such homomorphisms agree once they agree on every basis symbol. Hence the following calculations on symbols prove identities on the groups; all maps on zero groups are zero.

### Original calculation 2

Write $\sigma=[z_0,\ldots,z_q]$ and let $D_a\sigma$ denote deletion of position $a$, numbered from zero. For $a<b$, the term deleting original positions $a,b$ occurs in $d^2\sigma$ with coefficients $(-1)^{a+b-1}$ (delete $a$, then position $b-1$) and $(-1)^{a+b}$ (delete $b$, then position $a$). These sum to zero, and every term belongs to exactly one such pair. This also covers $q=1$, where both final symbols are $[\varnothing]$. For $q=0,-1$ the second boundary is zero by definition. Thus $d^2=0$ in all degrees.

### Original calculation 3

Fix $i$ and suppose $\sigma$ misses color $i$; let $k$ be the number of its colors less than $i$. In $dc_i\sigma$, deletion of the inserted vertex has coefficient $(-1)^k(-1)^k=1$ and gives $\sigma$. For an original vertex in position $a<k$, its deletion has coefficient $(-1)^{k+a}$, whereas its term in $c_id\sigma$ has coefficient $(-1)^{a+k-1}$. For $a\geq k$ these coefficients are respectively $(-1)^{k+a+1}$ and $(-1)^{a+k}$. Each pair cancels, so $(dc_i+c_id)\sigma=\sigma=(1-R_i)\sigma$. For $\sigma=[\varnothing]$ this calculation reads $dc_i[\varnothing]=d[(i,v_i)]=[\varnothing]$, with $c_id[\varnothing]=0$.

### Original calculation 4

If instead $\sigma$ contains color $i$ in position $k$, then $c_i\sigma=0$. Among the faces of $\sigma$, only $D_k\sigma$ misses color $i$, so $c_id\sigma=(-1)^k(-1)^kT_i\sigma=T_i\sigma$, where $T_i\sigma$ is obtained by replacing that vertex by $(i,v_i)$. Since $R_i\sigma=\sigma-T_i\sigma$, again $dc_i+c_id=1-R_i$. Together with the preceding step this identity holds on every nonzero degree, including the top degree (there every symbol contains $i$ and $c_i=0$); on the remaining zero groups it holds trivially. No equality between the original vertex and the chosen vertex was assumed.

### Original calculation 5

Multiplying $R_i=1-dc_i-c_id$ on the left and right by $d$, and using $d^2=0$, gives $dR_i=d-dc_id=R_id$. Set $P_0=1$ and $P_i=R_0\circ\cdots\circ R_{i-1}$ for $1\leq i\leq r$. Each $P_i$ commutes with $d$ by repeated substitution of $dR_j=R_jd$. Hence the stated sum $S=\sum_{i=0}^{r-1}P_ic_i$ satisfies
$$dS+Sd=\sum_{i=0}^{r-1}P_i(dc_i+c_id)=\sum_{i=0}^{r-1}(P_i-P_{i+1})=1-P_r.$$
The middle equality uses $P_iR_i=P_{i+1}$ with precisely the composition order in the statement, and requires no permutation of the factors.

### Original calculation 6

On a symbol of degree $-1\leq q\leq r-2$, at least one of the $r$ colors, say $j$, is missing. Every $R_i$ either kills a symbol or produces a difference of symbols with the same color list. Thus, when $P_r=R_0\circ\cdots\circ R_{r-1}$ is applied from right to left, every term reaching $R_j$ still misses $j$, and $R_j$ kills it. Therefore $P_r=0$ in the specified degrees, and the preceding identity gives $dS_q+S_{q-1}d=1$. In degree $-1$ only $i=0$ contributes to $S[\varnothing]$: for $i>0$, the factor $R_0$ kills $c_i[\varnothing]$. Consequently $S_{-1}[\varnothing]=[(0,v_0)]$ and $dS_{-1}=1$, consistently with $S_{-2}=0$.

### Original calculation 7

For a family $u_i:X_i\to Y_i$ with $u_i(v_i)=w_i$, applying $u$ to a symbol preserves its color list and hence every insertion position. If color $i$ is absent, $J(u)c_i^v\sigma$ and $c_i^wJ(u)\sigma$ are the identical signed symbol with inserted vertex $(i,w_i)$; if present both are zero. If color $i$ is present, both $J(u)R_i^v\sigma$ and $R_i^wJ(u)\sigma$ equal $J(u)\sigma-T_i^wJ(u)\sigma$; if absent both are zero. Thus $J(u)c_i^v=c_i^wJ(u)$ and $J(u)R_i^v=R_i^wJ(u)$ on the bases, including the empty symbol. Composing these equalities in the specified order and summing over $i$ proves $J_{q+1}(u)S_q^v=S_q^wJ_q(u)$. Injectivity of $u_i$ is unnecessary, since the calculation permits cancellation of coincident output symbols.

### Original calculation 8

For completeness an unreduced expansion gives the coefficient-list assertion explicitly. Let $C$ be the colors of $\sigma$. The $i$-th summand $P_ic_i\sigma$ is zero if $i\in C$. It is also zero if some $j<i$ is missing from $C$: after inserting color $i$, every preceding replacement preserves the color list, and $R_j$ kills every term. Otherwise let $k=\#\{j\in C:j<i\}$ and, for $A\subseteq\{0,\ldots,i-1\}$, let $\sigma_{i,A}$ be $\sigma$ with $(i,v_i)$ inserted and the vertices of colors in $A$ replaced by their chosen vertices. Distributing the two terms of each $R_j$ gives
$$P_ic_i\sigma=\sum_{A\subseteq\{0,\ldots,i-1\}}(-1)^{k+|A|}\sigma_{i,A}.$$
Indeed each subset records exactly the factors in which the negative replacement term was selected; replacements at different colors affect different positions and do not change any color. This list has $2^i$ terms, with repetitions and zero cancellation left uncollected. The list of indices, replacement choices and signs depends only on $r,C$. It never tests whether $x_j=v_j$, even when some terms coincide. Summing these lists proves the final assertion.

## Finite edge computation

The sandbox-only Python verifier edge-check.py passed on 363 basis faces for r=1 through 5, including the empty and top faces, checking every local identity, dR=Rd, the ordered-prefix telescope, proper-support vanishing and every individual subset expansion. It also passed 1884 face/map cases for all families of maps from a binary set to itself for r=1 through 3, including constant maps and images with changed chosen basepoints. These computations check finite edge cases; the complete general sign and support arguments are retained above. No Lean or build tool was used.

## Dry-run repair

The first server preflight rejected the abstract prefix node because its statement had no definition-node citation. I opened def-weil-pbc-module-chain-complex-homology and checked its statement: integer-indexed modules with d_(q-1) d_q=0, and the morphism convention d f=f d. I added this existing Mathlib definition leaf to the prefix statement and stmt_deps, explicitly viewing abelian groups as integer modules. This leaves the mathematical hypotheses and conclusions unchanged. The assembly citation now quotes the revised statement verbatim. This is a definition dependency, so it introduces neither a proof-route departure nor a dependency on the parent.


## Landing-return repair, 2026-10-22

The return names approved head bd7044db11d and a landing refusal because the side completion had not been promoted to the live queue DAG. I continued the retained sandbox, including its three nodes, original proof transcription, citations and actual search log; I did not recreate or discard that work. The authorized delivery tool rebuilt it against the current server DAG and completed its initial dry run at 26113940368 (not pushed). No direct git command was run in the shared repository.

I compared every sandbox node with the current shared DAG. The three child ids are still absent there. For the parent, only proof, proof_deps and split_report differ: the statement, statement dependencies, source, blueprint provenance and existing administrative metadata agree. The released stage-1 repair note explicitly reopens this otherwise reviewed parent and still requires at least two independent new tasks and an assembly of at most 3000 characters. The three-task allocation above meets that order. The delivery command performs the actual rebase and preserves current server-owned metadata.

I re-read the statements of all four assembly citations, and also the chain-complex definition used by the prefix child's statement. The current free-module definition still gives unique finite basis expansions; the current chain-complex definition still gives integer degrees, the square-zero relation and the stated chain-map indexing. The three child statements still supply respectively the two local identities, the ordered-prefix defect and support-annihilation criterion, and operator naturality plus the individual-summand subset expansion. Every saved citation quote remains a verbatim substring of the statement it cites. Thus no citation needs retargeting or an extra hypothesis. The current chapter, unit and direct-images paragraph (3) were re-read: this is still explicitly an agent expansion below that route, not a claim that the blueprint contains the calculation.

The fresh B-E review found doubled TeX backslashes in the decoded text of assembly steps 3 and 4 (for example before leq and sigma). I normalized them to single TeX backslashes without changing any mathematics. This repairs the retained delivery rather than making an unchanged re-push. All original calculations and search answers remain retained. The statements and search questions have not changed, so the existing logged Mathlib searches are reused. The upstream declaration search again found no matching completed project declaration; the complete Sheaf theorem still ends in sorry. No Lean or compiler was run.

## Fresh landing-return retry by Q136

The required first dry run of this retained split passed at 610b1780a54. I then compared the current shared node with all four saved node files: the parent differs only in proof, proof_deps and split_report; each child id is still absent. The released stage-1 repair note remains active, so the old reviewed eight-step proof does not supersede this re-split. I re-read all four assembly citations and the prefix statement's chain-complex definition. The four quotes in citations.json still occur verbatim in those statements. The saved search answers were read and reused because no statement or search question changed.

For this retry I clarified assembly step 3 itself: it now introduces I, covers the empty symbol's zero colors explicitly, states the telescoping identity with all degree indices, and identifies H_q with S_q through the actual P_(i,q+1)c_(i,q) formula. This makes the support and grading hypotheses checkable directly at the application. It changes no statement or dependency. The parent remains below 3000 characters and has no step above 2000 characters. The earlier landing-return repair and its preserved original arguments are retained above.

For B-E I rechecked that the new nodes are self-contained and statement-only, that their source places honestly identify agent expansions below direct-images paragraph (3), and that no SGA source is used. The single-color node supplies both square-zero and every local insertion identity; the prefix node supplies the defect and proper-support annihilation; the expansion node supplies individual operator naturality and summand formulas. The parent only extends on bases, instantiates those statements and adds finite composites and lists. The pointed-set hypothesis, r at least one, zero groups, augmented and top degrees, rightmost-first composition and possibly noninjective vertex maps were all checked against the current statements and the original sign calculation. The upstream project search still finds no complete matching declaration; the Sheaf theorem still has sorry. No Lean or compiler was run.
