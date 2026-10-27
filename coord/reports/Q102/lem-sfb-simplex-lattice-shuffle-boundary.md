# Worker report: Q102 / lem-sfb-simplex-lattice-shuffle-boundary

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-simplex-lattice-shuffle-boundary.json: repaired split, identical statement and statement dependencies; short assembly.
- lem-sfb-shuffle-mixed-corner-cancellation: statement, unsplit, no Mathlib match.
- lem-sfb-shuffle-horizontal-face-reindexing: statement, unsplit, no Mathlib match.
- lem-sfb-shuffle-vertical-face-reindexing: statement, unsplit, no Mathlib match.
- citations.json: every step/node pair with a verbatim statement quote.
- searches.jsonl: actual msearch.py calls; repair.py and returned-proof.json are sandbox-only working records.

## Attachments

None. Searched the project WeilConjectures/ for the exact blueprint tag and shuffle/lattice path concepts. The Sheaf/AlgebraicTopology/SimplexLatticeShuffleBoundary.lean file has real definitions but its joint boundary/augmentation/naturality theorem ends in sorry. Neither its helper definitions nor the unrelated evaluation_shuffle or Koszul permutation-sign declarations prove the item or any complete new node. No Lean was written or compiled.

## Wanted literature

WANTED: Weibel, An Introduction to Homological Algebra, section 8.5, unnormalized shuffle boundary calculation, for the item and each of the three new nodes. literature/LIST.md says the book has no freely obtainable local copy; no download was attempted. The source actually read is the main-20261015 sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3); it supplies the application and not the combinatorial calculation. All the arguments here are explicitly agent-written. No SGA source is used and no Stacks tag is invented for this combinatorics.

## Repair and discrepancies

The dispatcher said a delivered version and report would be retained; the sandbox instead contained only .brief2 through .brief5. I copied the current shared node (which contains exactly the returned ten-step proof) and preserved its statement, metadata, old search records and source. There was no retained report or search log to discard. The existing proof was correct but too large under the human's re-split decision. All ten original arguments are accounted for below; the three substantial arguments are now independently claimable unsplit statements, not a renamed whole boundary lemma. New nodes have no proof steps or proof dependencies. No target statement, chapter route or unit record was changed.

## Not duplicates

lem-sfb-shuffle-mixed-corner-cancellation vs lem-sfb-simplex-lattice-shuffle-boundary: only the sign encoding and mixed-interior labeled involution; it does not give horizontal or vertical terms, the chain identity, augmentation or naturality.
lem-sfb-shuffle-horizontal-face-reindexing vs lem-sfb-simplex-lattice-shuffle-boundary: a signed bijection for horizontal labeled faces of arbitrary evaluated words; it gives neither mixed cancellation nor the other direction nor the assembled boundary identity.
lem-sfb-shuffle-vertical-face-reindexing vs lem-sfb-simplex-lattice-shuffle-boundary: a signed bijection for vertical labeled faces, strictly one proper part of the chain calculation.
The three new statements are distinct: the first pairs mixed corners, the second collapses equal H letters with horizontal face signs, the third collapses equal V letters with Koszul signs. Searches of all DAG statements and the whole blueprint for shuffle, lattice path, mixed corner, horizontal face and vertical face found no existing assertion of these bijections. Opened the candidate Cech-horizontal, prism-boundary, prism-horn, relative-join and parent bicosimplicial/product-bar statements: Cech uses subset restriction coordinates, prisms assert horn pushouts, and the two parents assert derived comparisons, none the present word bijections. Parents are downstream and are not cited, avoiding cycles. There are no shared Stacks tags to disambiguate.

## Mathlib search review

Every new node has real leanfinder, leansearch, loogle and grep queries, with the exact recorded text and returned digest in its mathlib_searches. The two semantic queries for each give different phrasings. All services answered. Read every result: generic permutation sign/sign_swap handles only the sign subcalculation of the mixed node; simplex degeneracy normal forms concern one simplicial object; face-face relations and alternating-face square-zero do not give either two-direction word bijection. Read Perm/Fin.lean lines 497–510, ProdStdSimplex.lean lines 40–73 and the relevant GeneratorsRelations/NormalForms and AlternatingFaceMapComplex declarations. In particular product-simplex face evaluation does not supply the inverse word construction or any inversion count. No result states a whole new node or specializes to it in one line. Existing item searches are retained because its statement/search question did not change.

## Review by Q102

I read the source paragraph, chapter record sec-six-functors-basics and inherited unit sk-thm-sf-ctf-stability, and compared the full existing Lean theorem to the item. The inherited unit record is filed under sec-six-functors while the node belongs to sec-six-functors-basics; that inherited metadata was not altered. The ancestor tool returns None, so each new blueprint.from.node remains null, with the original item's id prepended to via and a precise place rather than a fabricated ancestor. Whole-blueprint searches found no same_as match.

For new step 1 I opened def-weil-pbc-module-chain-complex-homology: it defines d squared zero, chain maps and extension outside nonnegative degrees by zero, exactly what the step uses. The deletion sign cancellation and augmentation 1-1 are written out, not attributed to an unstated theorem. The free bases are finite in each degree and all maps extend linearly.

For step 2 I read the full mixed-corner node: it explicitly equates the shuffle permutation sign with the V-before-H inversion sign and states both the fixed-point-free involution and the vanishing signed sum after evaluation. Thus the step uses its statement, not a hidden proof. All its hypotheses hold with X=[p], Y=[q]; repeated vertices are explicitly allowed. The partition of all labeled faces is elementary and stated with both endpoint and interior rules.

For step 3 I read both reindexing nodes. Their statements provide every needed evaluated-string equality, coefficient formula and inverse bijection including both endpoints. The horizontal node assumes a>0 and is used only then; for a=0 its labeled set is empty. The vertical node assumes b>0 and is used only then; for b=0 it is empty. Thus the two finite sums really are the two differential terms, with no missing edge cases or unrecorded facts. This step does not assume evaluation is injective. The free-group equalities restrict to monotone strings since all the evaluated paths and their deleted strings remain coordinatewise weakly increasing. For n=0 no shorter-word lemma is applied.

For step 4 the unique empty word and the vertex augmentations compute both maps on a basis pair. Step 5 proves postcomposition term by term using the unchanged index counts and signs, and separately checks deletion and augmentation; no naturality theorem is silently imported. Each elementary step fits a few direct computations, and no new non-elementary step exceeds 2000 characters. citations.json quotes the exact statement of every cited node.

I checked the mixed swap changes only the deleted intermediate vertex and exactly one inversion. In horizontal interiors, i=A_k, t=B_k and k=i+t, so the removed H contributes t inversions and the coefficient is (-1)^(i+2t). Initial H removes zero inversions; terminal H removes b. In vertical interiors the removed V contributes a-i inversions, giving (-1)^(a+j); initial V removes a, terminal V removes zero. The shorter word inverse splits the i-th H or j-th V, counted from one, so the inverse exists precisely for interior indices. At a=1 or b=1 there are two separately labeled endpoint cases even when they evaluate to the same generator. At a=b=0 the boundary vanishes and the empty word preserves augmentation. At a=0 or b=0 there are no mixed corners and just the remaining factor's cases. Arbitrary repeated entries and noninjective postcomposition never affect labeled bijections. The exhaustive finite checks recorded below independently test these claims.

## Work remaining

Only stage 1 is authorized. The three new nodes are deliberately delivered unsplit for separate workers; no proof is hidden in a new node's proof field. Their complete intended arguments are preserved verbatim below from the returned proof, so future workers can recover the calculations. No mathematical issue prevents the split.

## Preservation of every returned argument

Returned step 1 is retained as item step 1 (complex identities and validity of shuffle summands). Returned step 2 is divided between the mixed node's permutation-sign assertion and item step 2's labeled boundary expansion. Returned step 3 is the mixed node's full involution, evaluated equality and cancellation. Returned steps 4–5 are the horizontal node's interior and endpoint bijections and inversion equalities. Returned steps 6–7 are the vertical node's corresponding bijections and equalities. Returned step 8 is retained in item steps 2–3 as the exhaustive partition, bilinear assembly, repeated-entry justification and zero-degree convention. Returned steps 9–10 are retained in item steps 4–5 as augmentation and termwise naturality. For avoidance of any loss in shortening the assembly, the exact original proof is reproduced as argument material for the new unsplit nodes and remaining elementary steps:

### Returned step 1

All groups and maps in the statement are defined on finite bases in each degree and extended linearly. Deletion preserves weak increase. For any string of degree at least two, deleting original positions $i<j$ in the two possible orders gives the same remaining string with coefficients $(-1)^{i+j-1}$ and $(-1)^{i+j}$, which cancel. The composite differential in degree one is zero by the degree-zero convention. Also the augmentation of the boundary of an edge is $1-1=0$. Thus the three displayed constructions are augmented chain complexes in the convention of [def-weil-pbc-module-chain-complex-homology]. For a shuffle, $A_k,B_k$ are nondecreasing and in the stated index ranges, so every summand is a valid generator of $V$.

### Returned step 2

Encode a partition by a word $w$ of length $n=a+b$ with $a$ letters $H$ in the positions of $\mu$ and $b$ letters $V$ in those of $\nu$. Write $z(w)$ for its pair string and $I(w)$ for the number of pairs of positions in which a $V$ precedes an $H$. The concatenated permutation $(\mu,\nu)$ has precisely these inversions: each block is increasing and a cross-block inversion is a vertical position smaller than a horizontal position. Hence its sign is $s(w)=(-1)^{I(w)}$. For $n>0$, expansion of the left side of the boundary identity is the finite sum over labeled pairs $(w,k)$, $0\leq k\leq n$, of $s(w)(-1)^k$ times $z(w)$ with vertex $k$ omitted. We compare these labeled terms before collecting equal generators.

### Returned step 3

Consider $0<k<n$ where letters $k-1,k$ of $w$ are different. Swap these two letters to obtain $w'$, keeping $k$ fixed. This is a fixed-point-free involution on these labeled pairs. Before the two moves and after the two moves the lattice vertices agree; their only possibly different vertex is the deleted vertex $k$. Thus the surviving pair strings agree entry by entry, including when $u$ or $v$ has repetitions. Only the inversion between the two adjacent letters changes, so $s(w')=-s(w)$. The coefficients $s(w)(-1)^k$ and $s(w')(-1)^k$ therefore cancel pairwise.

### Returned step 4

Suppose instead that $0<k<n$ and both neighboring letters are $H$. Put $i=A_k$ and $t=B_k$, so $k=i+t$ and $1\leq i<a$. Remove the vertex between the two horizontal moves and replace those two letters by a single $H$, giving a word $\bar w$ with $a-1$ horizontal letters and $b$ vertical letters. The deleted pair string is exactly the $\bar w$ summand for $(u_0,\ldots,\widehat u_i,\ldots,u_a)$ and $v$. One of the two identical horizontal moves has been removed; its inversions are the $t$ preceding vertical moves. Hence $I(w)=I(\bar w)+t$, and $s(w)(-1)^k=s(\bar w)(-1)^{t+i+t}=s(\bar w)(-1)^i$. For each fixed $i$ and each such $\bar w$ the inverse operation splits its $i$-th horizontal move (counted from one) into two horizontal moves; this gives exactly one labeled pair $(w,k)$.

### Returned step 5

The horizontal endpoints give the missing horizontal faces. If $k=0$ and the first letter is $H$, remove that letter; no inversion is removed, and the remaining string is the shuffle of $(u_1,\ldots,u_a)$ with $v$. Its coefficient is $s(\bar w)$, the face sign for $i=0$. If $k=n$ and the last letter is $H$, remove that letter; it has all $b$ vertical letters before it, so $I(w)=I(\bar w)+b$ and $s(w)(-1)^n=s(\bar w)(-1)^{b+a+b}=s(\bar w)(-1)^a$. The remaining string is the shuffle of $(u_0,\ldots,u_{a-1})$ with $v$. Prepending or appending $H$ gives the inverse bijection with the shorter shuffle words. For $a=1$ there are no interior horizontal faces, and these two distinct labeled endpoint cases still apply; for $a=0$ there are no horizontal cases at all.

### Returned step 6

If $0<k<n$ and the two neighboring letters are $V$, put $i=A_k$, $j=B_k$, so $k=i+j$ and $1\leq j<b$. Collapse the two vertical moves to one, obtaining $\bar w$ with $a$ horizontal letters and $b-1$ vertical letters. The surviving string is its shuffle on $u$ and $(v_0,\ldots,\widehat v_j,\ldots,v_b)$. The removed vertical move has exactly $a-i$ horizontal moves after it; hence $I(w)=I(\bar w)+a-i$. Consequently $s(w)(-1)^k=s(\bar w)(-1)^{a-i+i+j}=s(\bar w)(-1)^{a+j}$. For each fixed $j$ and shorter word, splitting its $j$-th vertical move (counted from one) recovers the unique original labeled pair.

### Returned step 7

At $k=0$ with first letter $V$, removal of that letter removes $a$ inversions. The remaining string is the shuffle on $u$ and $(v_1,\ldots,v_b)$ with coefficient $s(\bar w)(-1)^a$, as required for $j=0$. At $k=n$ with last letter $V$, no inversion is removed. The remaining string is the shuffle on $u$ and $(v_0,\ldots,v_{b-1})$ with coefficient $s(\bar w)(-1)^{a+b}$, as required for $j=b$. Prepending or appending $V$ is the inverse bijection. For $b=1$ these are the only vertical cases, and for $b=0$ there are none.

### Returned step 8

For $n>0$ these cases exhaust the expanded left side: an endpoint has a first or last letter of exactly one type, and an interior vertex has either different neighbors or two horizontal or two vertical neighbors. After the mixed terms cancel, the horizontal bijections give precisely $\sum_{i=0}^a(-1)^i\sigma((u_0,\ldots,\widehat u_i,\ldots,u_a)\otimes v)$ when $a>0$, while the vertical bijections give precisely $\sum_{j=0}^b(-1)^{a+j}\sigma(u\otimes(v_0,\ldots,\widehat v_j,\ldots,v_b))$ when $b>0$. This is the asserted boundary identity. No injectivity of the evaluation of labeled strings was used. If $n=0$, both boundaries and both omitted terms are zero. Equality on basis pairs extends bilinearly to all elements.

### Returned step 9

In degree zero $a=b=0$ and the unique word is empty, with sign $1$; $\sigma_0$ sends the pair of vertices $(u_0,v_0)$ to that pair vertex. Both $\epsilon_V\sigma_0$ and $\epsilon_p\otimes\epsilon_q$, under $\mathbf Z\otimes_{\mathbf Z}\mathbf Z\cong\mathbf Z$, take every such basis pair to $1$. Linearity proves the augmentation identity.

### Returned step 10

For monotone $f:[p]\to[p']$ and $g:[q]\to[q']$, the shuffle term indexed by $w$ after postcomposition has vertex $(f(u_{A_k}),g(v_{B_k}))$. This is exactly the $w$ term obtained by first postcomposing $u,v$ and then shuffling; the indexing words and signs do not change. Summing proves naturality. Postcomposition also commutes entry by entry with deletion and sends a vertex to a vertex, so these are maps of the augmented complexes. Noninjective maps can identify generators, but equality term by term before collecting coefficients remains valid.

Assembly text length: 2272 characters. Three new statements have lengths 1344, 1661, 1664 characters including their self-contained common definitions.

## Finite verification

Exhaustive Python check: a,b=0..4; 1848 labeled word/deleted-vertex cases checked for sign, mixed involution, reindexing bijections and inverse operations; 3844 arbitrary binary sequence pairs (including repeats and nonmonotone sequences) checked for the signed boundary identity; four identity/constant postcomposition pairs checked for every sequence pair. All passed. The a=b=0 shuffle preserves augmentation (single empty word with sign 1). This is a finite sanity check, not a Lean proof.

## Preflight repair

The first server preflight rejected the three new nodes because their statements contained no node citations. I opened def-weil-pbc-free-module: it defines basis and the free module as unique finite linear combinations, exactly the formal integral combinations used here. All three new statements now explicitly regard strings as basis symbols in the corresponding free integral module and cite that definition as a statement dependency. This makes the existing free-module interpretation explicit; the combinatorial assertions and search questions did not change. No proof or new hypothesis was added.

## Repair of L promotion return (2026-10-22)

Return at 06:46 UTC, returned head b10d6299221: the reader approved the split, but landing refused the side completion because the live queue DAG did not yet contain it. This repair retains the complete prior sandbox delivery and searches. The required initial dry run finished successfully at 48ade92bf4d on the current origin/sheaf-dag; deliver.py fetches that branch and builds a new commit over it, preserving maintainer-owned fields. No repository git command was run by this worker.

I compared the preserved returned-proof.json with the current shared item's full proof: they are identical. The retained sandbox item and current shared item differ only in proof, proof_deps, proof_origin and split_report, precisely the old-to-new re-split; statement, stmt_deps, source, blueprint, Lean record and review metadata agree. All three statement-only lemmas remain absent from the current shared DAG. The promotion return supplies no mathematical correction to undo, and the released stage-1 repair note still explicitly requires at least two new nodes and at most 3000 assembly characters.

I re-read every cited statement, including both external definitions: def-weil-pbc-module-chain-complex-homology still defines integer chain complexes, extension by zero and chain morphisms; def-weil-pbc-free-module still defines a basis by unique finite linear combinations. The first citation quote remains verbatim. The other three quotes are the complete retained lemma statements. No hypothesis or cited result has changed. I made one proof clarification in item step 3: the generic free-group identities of the three lemmas restrict to the subgroup on monotone strings via inclusion of bases. Every path and deleted path lies in that subgroup, so no theorem about arbitrary strings is silently identified with a different complex. This is an elementary basis inclusion, requiring no additional node. The new assembly remains below 3000 characters, and both non-elementary steps remain below 2000 each.

I again checked the sign at mixed corners, horizontal endpoints (0 and b removed inversions), vertical endpoints (a and 0), zero factor degrees, repeated generators, augmentation and noninjective postcomposition. The existing logged semantic, Loogle and grep queries concern the unchanged statements and are retained without fabricated or redundant searches. The earlier full argument mapping, source disclosures and review signature remain part of this report. No target, chapter or unit route was changed.

## Latest promotion-return repair and review by Q102 (2026-10-22)

The current return in coord/returns/Q102.md names returned head 83d7c670206 at 11:07 UTC and asks for rebasing onto the current DAG and re-reading changed citations. I retained the delivered sandbox files, report, citations and searches; the older b10d6299221 discussion above is historical. The required first dry run in this repair exited OK at e8bc042e470. The delivery tool builds on the current fetched server branch; I ran no git command in the read-only repository.

The retained returned-proof.json still exactly equals the shared node's ten-step proof. Comparing every JSON field of the retained item with the current shared node found differences only in proof, proof_deps, proof_origin and split_report. In particular statement, statement dependencies, source, blueprint, Lean record and maintainer review fields agree. The three new lemma files are still absent from the shared DAG. The released stage-1 repair order still calls for at least two new statement-only nodes and assembly under 3000 characters, so the earlier reviewed ten-step split does not supersede this repair.

I re-read both external dependency statements in full and the full statements of all three new lemmas. No cited statement needed replacement: the chain-complex definition explicitly gives the differential identity, zero extension and chain morphisms used in step 1; the free-module definition supplies unique finite basis expansions used by the new nodes. Step 2 takes its sign equality and mixed-corner cancellation from the mixed node, with n>0. Step 3 takes its two signed bijections from the horizontal and vertical nodes, used only when a>0 and b>0 respectively, and handles the empty degree cases separately. Their statements allow arbitrary sequences and repeated entries. I now explicitly instantiate their sets as X=[p], Y=[q], and prove restriction to the actual monotone-string complex coefficient by coefficient: all nonmonotone coefficients vanish, and the remaining coefficient equalities are precisely equality in V(p,q). This replaces an implicit basis-subgroup identification and is a concrete proof adjustment beyond rebuilding a commit. Steps 4 and 5 compute augmentation and postcomposition on each basis element; they need no new theorem.

Against delivery-errors B–E: each new node remains self-contained, statement-only, with real logged searches retained for its unchanged statement and no fabricated Stacks citation. All four step/node citation pairs were checked against verbatim statement substrings. No cited theorem is applied with missing hypotheses, no proof of a dependency is used instead of its statement, and the three new nodes have no proof edges that could create a cycle. The shared DAG and whole-blueprint duplicate search still finds no replacement for these three statements (blueprint search for shuffle returns zero). Each lemma is strictly smaller than the assembled boundary/augmentation/naturality result. I checked the initial and terminal inversion counts again: horizontal 0 and b, vertical a and 0, giving the claimed coefficients; a=b=0, a=1, b=1, repeated entries and noninjective postcomposition remain covered by the retained calculation and finite verification. The source paragraph was re-read and still only motivates the application; all combinatorial proofs are honestly marked agent-written, with Weibel 8.5 WANTED. No route, target, chapter or unit statement changed.
