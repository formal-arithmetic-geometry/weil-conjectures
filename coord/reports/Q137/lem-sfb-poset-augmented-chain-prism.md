# Repair report: lem-sfb-poset-augmented-chain-prism

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-poset-augmented-chain-prism.json`: unchanged statement; three-step assembly of two weak-tuple lemmas.
- `dag/nodes/sec-six-functors-basics/lem-sfb-poset-weak-chain-normalization.json`: statement, unsplit; no exact or one-line Mathlib match. Carries old steps 1–4 (2467 characters of argument).
- `dag/nodes/sec-six-functors-basics/lem-sfb-poset-weak-prism-identity.json`: statement, unsplit; no exact or one-line Mathlib match. Carries old steps 5–8 (2229 characters of argument).
- `citations.json`: verbatim statements supporting every cited parent-step/node pair.

## Attachments

None. Searched the entire project `lean/WeilConjectures` for the blueprint tag, prism, and weak tuples. There is no matching project declaration. Read `Sheaf/AlgebraicTopology/AugmentedPosetChains.lean` and `AugmentedPosetChainPrism.lean`: boundary_laws, map_comm, map_id, map_comp, and prism_identity all have sorry proofs. They are reference statements, not finished attachments.

## WANTED

None: Stacks simplicial.tex is available.

## What was wrong and how this repairs the return

The returned proof assigned 4696 characters of independent tuple calculations to one item. Its previous review was mathematically positive, but the human now requires at least two comparably sized new statement-only nodes. This repair creates exactly two, whose respective retained argument sizes are 2467 and 2229 characters. Neither restates the parent: the first identifies a weak-tuple quotient and its functorial structure; the second is an identity on the raw weak modules together with preservation of their repeated submodules. The parent's conclusion is on augmented strict chains, obtained by the explicit quotient assembly. No target or item statement is changed.

The sandbox initially contained only dispatcher markers, with no node, report, or searches.jsonl to reuse. I copied the returned item from the current read repository; its full eight-step argument and the return's described lengths agree. All existing metadata, source, Lean records and blueprint provenance are preserved. The new searches are actual calls to the authorized msearch command; their log records are copied exactly into the corresponding node. The item's inherited searches remain intact.

## Source and search review

Read GOAL.md; the chapter sec-six-functors-basics and unit sk-thm-sf-ctf-stability; the three-level route in SETUP.md; stages/1-dag.md; and delivery-errors.md B–E in both copies. The inherited combinatorial proof is agent-written beneath the direct-image route, and blueprint_refs ancestor returns None. This repair preserves that ancestry and its via list, prepending the item for the two children. Searches with blueprint_refs for weak tuple, weakly increasing, strict chains, prism, degenerate, and normalization found no blueprint statement of either new lemma. Whole-DAG keyword and tag searches were also read; the actual plausible overlaps are distinguished below. No chapter or unit route is replaced.

For the parent and each new node I read Stacks simplicial.tex lines 4739–4846: equation-homotopy-to-homotopy and lemma-homotopy-s-N. The tags file identifies them as 019R and 019S. The source expands the double sum, cancels the off-junction terms, and telescopes the remaining faces. The weak-poset model, killing repetitions, and degree -1 convention are explicitly agent adaptations, not assertions falsely attributed verbatim to Stacks. The first new node serves the model/quotient obligations from old steps 1–4; the second serves the actual prism cancellation and descent obligations from old steps 5–8. Their statements introduce every module, differential, degeneracy span, entrywise map, and pivot operator they use. The second node explicitly cites def-weil-pbc-module-chain-complex-homology for its integer-degree differential convention; I opened that definition and checked its d_n:C_n to C_(n-1) sentence. This is a notation/definition citation, not a theorem borrowed from its proof.

For both new nodes I ran LeanFinder, Loogle, grep and LeanSearch, and a second LeanFinder phrasing. LeanSearch for the second node was rate-limited and is recorded unavailable, not a negative result. Read the returned hits and the actual source in AlternatingFaceMapComplex.lean:53–150, SimplicialObject/ChainHomotopy.lean:35–175 and SimplicialSet/Homology/Nondegenerate.lean:35–100. The generic simplicial declarations require a constructed poset simplicial object, normalization comparison or simplicial homotopy; they do not give the augmented quotient or the specific weak prism with degeneracy preservation in one line. In particular toChainHomotopy.hom_eq has a negative signed sum and ordinary natural degrees; the identification with this positively signed prism and its integer augmentation is further work. The unrelated representation resolutions and DoldKan normalization maps do not remove these obligations.

## Review by Q137

I checked the cited statements against each of the three final steps, not merely their names. Step 1 uses the first new lemma's surjective chain map q, kernel D and chain isomorphism W/D with C; this is exactly its assertion. Step 2 uses that same lemma's entrywise chain maps, preservation of D, their identity/composition equations, and the explicit image formula under the quotient identification. Passing these equations through the specified isomorphisms gives the strict-chain functoriality without an unstated comparison lemma. Step 3 uses the second new lemma's actual H formula, preservation of D and identity in every integer degree, and the first lemma's quotient chain map and surjectivity. Factoring the finitely defined linear operators through the quotient gives qH=hq on every generator. Applying q to the equality and cancelling the surjective q is elementary algebra, written explicitly in the parent. Each used sentence/formula is quoted verbatim in citations.json.

The new statements have the same commutative coefficient ring and finite partially ordered sets as the item. The monotone-map hypotheses and pointwise f<=g condition are explicitly present wherever the prism is used. Partial-order antisymmetry, not a preorder assumption, is needed to turn any repeated weak tuple into an adjacent repetition. No nonemptiness, characteristic, or nonzero-ring assumption is introduced. I checked the signs against the source orientation: with the parent's (-1)^i, the junction terms are A_i-A_(i+1), hence g-f. The first node asserts the full quotient and naturality, not just a definition of normalization; the second states preservation of D as well as the identity, so there is no hidden descent lemma.

Against delivery-errors B: both children are self-contained, have only statements and no proof/proof_deps, give the precise source labels with agent-adaptation caveat, use ordinary TeX escapes, carry complete blueprint fields, and have searches actually logged. Against C: only the two opened child statements are used in the parent; no proof of a definition is invoked as a theorem, and both children have no dependency path to the parent. Against D: the two separate raw weak-chain arguments are retained in full below and assigned to distinct unsplit nodes of comparable size; no single node carries the entire strict-chain theorem. Against E: I verified augmentation, repeated tuples and empty-poset cases, checked the exact modules and source/target degrees, and wrote the quotient equation instead of saying merely that the identity transports. No statement dispute was found. There is no parent proof step longer than 2000 characters.

## Not duplicates

lem-sfb-poset-weak-chain-normalization vs def-sfb-augmented-poset-chains: the existing node defines the strict-chain complex only; it does not assert a weak-tuple quotient comparison or a weak prism identity.

lem-sfb-poset-weak-chain-normalization vs lem-sfb-continuous-cochain-finite-index-transfer: the existing node constructs transfer on continuous group cochains for an open subgroup; it does not state an augmented weak-poset chain calculation.

lem-sfb-poset-weak-chain-normalization vs lem-sfb-poset-augmented-chain-prism: the existing parent is the final strict-chain prism theorem, including functoriality; this node isolates a raw weak-chain intermediate argument and does not assert the final strict-chain theorem.

lem-sfb-poset-weak-chain-normalization vs lem-sfb-product-chain-proper-interval-homology: the existing node computes rational homology of proper intervals of products of finite chains; it does not state a general weak-chain comparison or a prism operator.

lem-sfb-poset-weak-chain-normalization vs lem-weil-pbc-coskeleton-free-homology-comparison: the existing node is a homology-sheaf comparison for coskeletal simplicial presheaves; its hypotheses and conclusion do not give a weak-poset quotient or this prism formula.

lem-sfb-poset-weak-chain-normalization vs lem-weil-pbc-simplicial-homotopy-free-chain-homotopy: the existing node takes a supplied simplicial homotopy and asserts existence of a nonnegative free-chain homotopy; it neither identifies weak-poset quotients nor gives this explicit prism, degeneracy preservation and integer augmentation.

lem-sfb-poset-weak-prism-identity vs def-sfb-augmented-poset-chains: the existing node defines the strict-chain complex only; it does not assert a weak-tuple quotient comparison or a weak prism identity.

lem-sfb-poset-weak-prism-identity vs lem-sfb-continuous-cochain-finite-index-transfer: the existing node constructs transfer on continuous group cochains for an open subgroup; it does not state an augmented weak-poset chain calculation.

lem-sfb-poset-weak-prism-identity vs lem-sfb-poset-augmented-chain-prism: the existing parent is the final strict-chain prism theorem, including functoriality; this node isolates a raw weak-chain intermediate argument and does not assert the final strict-chain theorem.

lem-sfb-poset-weak-prism-identity vs lem-sfb-product-chain-proper-interval-homology: the existing node computes rational homology of proper intervals of products of finite chains; it does not state a general weak-chain comparison or a prism operator.

lem-sfb-poset-weak-prism-identity vs lem-weil-pbc-coskeleton-free-homology-comparison: the existing node is a homology-sheaf comparison for coskeletal simplicial presheaves; its hypotheses and conclusion do not give a weak-poset quotient or this prism formula.

lem-sfb-poset-weak-prism-identity vs lem-weil-pbc-simplicial-homotopy-free-chain-homotopy: the existing node takes a supplied simplicial homotopy and asserts existence of a nonnegative free-chain homotopy; it neither identifies weak-poset quotients nor gives this explicit prism, degeneracy preservation and integer augmentation.

lem-sfb-poset-weak-chain-normalization vs lem-cbc-normalized-simplex-chain-diagonal: the existing lemma concerns unaugmented standard totally ordered simplices and their tensor diagonal, not arbitrary finite posets with degree -1 and these weak-tuple/prism obligations.

lem-sfb-poset-weak-chain-normalization vs lem-coef-simplicial-latching-degenerate-subset: the existing lemma identifies a set-valued latching colimit with degenerate simplices, not the repeated-tuple module subcomplex, quotient chain isomorphism, or signed prism identity.

lem-sfb-poset-weak-prism-identity vs lem-cbc-normalized-simplex-chain-diagonal: the existing lemma concerns unaugmented standard totally ordered simplices and their tensor diagonal, not arbitrary finite posets with degree -1 and these weak-tuple/prism obligations.

lem-sfb-poset-weak-prism-identity vs lem-coef-simplicial-latching-degenerate-subset: the existing lemma identifies a set-valued latching colimit with degenerate simplices, not the repeated-tuple module subcomplex, quotient chain isomorphism, or signed prism identity.

lem-sfb-poset-weak-chain-normalization vs lem-sfb-equivariant-continuous-cochain-prism: the existing node concerns continuous equivariant function cochains on a topological group over a field, with a finite permuted family of self-maps; it neither constructs weak poset chain modules over an arbitrary commutative ring nor identifies their repeated-tuple quotient with augmented strict chains.

lem-sfb-poset-weak-prism-identity vs lem-sfb-equivariant-continuous-cochain-prism: the existing node proves a degree-lowering finite-family homotopy on nonnegative continuous group cochains, not the degree-raising prism for two comparable monotone maps on weak poset chains; it gives neither preservation of the repeated-tuple span nor the fixed degree -1 augmentation. Dualizing or constructing a poset-to-group comparison would require additional arguments and is not a specialization of its statement.

## Preserved argument for the two unsplit nodes

The following is the full returned argument, retained verbatim as the future workers’ starting material. It is report material, not proof steps on the unsplit nodes. Every argument of the old proof is assigned; no calculation was deleted.

### lem-sfb-poset-weak-chain-normalization

Old step 1:

For a poset $S$, let $W_n(S)$ be the free $R$-module on weakly increasing tuples $(x_0,\ldots,x_n)$ for $n\geq0$, with $W_{-1}(S)=R[\varnothing]$ and zero below $-1$. Define $d$ by alternating deletion and $d[x]=[\varnothing]$. For positions $a<b$, deleting $a$ then the original $b$ has coefficient $(-1)^{a+b-1}$, whereas deleting $b$ then $a$ has coefficient $(-1)^{a+b}$; the resulting tuples agree. These pairs exhaust $d^2$ for $n\geq2$. For $n=1$, $d^2[x_0,x_1]=[\varnothing]-[\varnothing]=0$, and for $n\leq0$ the next differential is zero. Thus $W(S)$ is a chain complex in the sense of [def-weil-pbc-module-chain-complex-homology].

Old step 2:

Let $D_n(S)\subseteq W_n(S)$ be spanned by tuples with a repetition, and put $D_n(S)=0$ for $n\leq0$. A repeated weak tuple has adjacent equal entries $x_j=x_{j+1}$: any equality at separated positions forces all intervening entries equal by antisymmetry. Deleting position $j$ or $j+1$ gives identical tuples with opposite coefficients; every other deletion retains these two adjacent equal entries. Hence $dD_n\subseteq D_{n-1}$. The quotient $W_n/D_n$ is identified with the free module on strict tuples by killing repeated basis tuples and keeping strict ones: this map and inclusion of strict generators are inverse after taking the quotient. In degree $-1$ it is the identity of $R$. The induced differential is exactly that of $C(S;R)$, so this also verifies the complex specified in the statement.

Old step 3:

For a monotone $u:P\to Q$, entrywise application defines $W(u)_n$ on each free basis and is the identity in degree $-1$. It commutes with each vertex deletion, so $dW(u)=W(u)d$ in degrees $n\geq1$; in degree zero both composites send every vertex to $[\varnothing]$, and below zero both are zero. Equal adjacent entries have equal images, so $W(u)D(P)\subseteq D(Q)$. Therefore it induces a chain map on $W/D=C$, exactly $u_*$ from the statement; the termwise commutation is precisely the chain-map condition of [def-weil-pbc-module-chain-complex-homology].

Old step 4:

Entrywise identity fixes every tuple and the empty generator. For monotone $u:P\to Q$, $v:Q\to S$, entrywise $(v\circ u)$ equals successive entrywise application of $u$ and $v$, including in degree $-1$. These equalities pass to the quotients, giving $(\mathrm{id}_P)_*=\mathrm{id}_{C(P;R)}$ and $(v\circ u)_*=v_*u_*$. In particular, if $u$ collapses a strict tuple to a repeated tuple, every further image is still repeated, in agreement with the zero convention.

### lem-sfb-poset-weak-prism-identity

Old step 5:

For a weak tuple $x=(x_0,\ldots,x_n)$ put $T_i(x)=(f(x_0),\ldots,f(x_i),g(x_i),\ldots,g(x_n))$ and $H_n[x]=\sum_{i=0}^n(-1)^i[T_i(x)]$, with $H_{-1}=0$ and zero lower down. Each $T_i$ is weakly increasing: monotonicity handles the two blocks and $f(x_i)\leq g(x_i)$ handles their junction. If $x_j=x_{j+1}$, then $i\leq j$ leaves the repeated pair in the $g$ block, and $i\geq j+1$ leaves it in the $f$ block. Thus every summand is repeated and $H_nD_n(P)\subseteq D_{n+1}(Q)$. The induced map on the quotients is the displayed $h_n$.

Old step 6:

Fix $n\geq1$, and write $\delta_j$ for deleting position $j$. Expand $dH_n[x]$ into terms $(-1)^{i+j}[\delta_jT_i(x)]$. For $j<i$, one has $\delta_jT_i(x)=T_{i-1}(\delta_jx)$, whose term in $H_{n-1}d[x]$ has coefficient $(-1)^{i-1+j}$ and cancels it. For $j>i+1$, one has $\delta_jT_i(x)=T_i(\delta_{j-1}x)$, whose term in $H_{n-1}d[x]$ has coefficient $(-1)^{i+j-1}$ and cancels it. These pairings exhaust the latter sum: a term there has prism index $r\in\{0,\ldots,n-1\}$ and deleted original index $k\in\{0,\ldots,n\}$; if $k\leq r$ its partner is $(i,j)=(r+1,k)$ in the first case, while if $k>r$ its partner is $(i,j)=(r,k+1)$ in the second case.

Old step 7:

Only $j=i$ and $j=i+1$ remain from $dH_n$. Define $A_i=(f(x_0),\ldots,f(x_{i-1}),g(x_i),\ldots,g(x_n))$ for $0\leq i\leq n+1$, with empty end blocks permitted. The $j=i$ face is $A_i$ with coefficient $(-1)^{2i}=1$; the $j=i+1$ face is $A_{i+1}$ with coefficient $(-1)^{2i+1}=-1$. Hence $dH_n[x]+H_{n-1}d[x]=\sum_{i=0}^n([A_i]-[A_{i+1}])=[g(x_0),\ldots,g(x_n)]-[f(x_0),\ldots,f(x_n)]$. This is $W(g)[x]-W(f)[x]$. Linearity gives the identity on all of $W_n(P)$, and the quotient maps of steps 2, 3 and 5 give $dh+hd=g_*-f_*$ on $C_n(P;R)$ for $n\geq1$.

Old step 8:

In degree zero, $H_0[x]=[f(x),g(x)]$, so $dH_0[x]=[g(x)]-[f(x)]$ and $H_{-1}d[x]=0$, even when the two vertices coincide. In degree $-1$, $d_0H_{-1}+H_{-2}d_{-1}=0$ and $W(g)_{-1}-W(f)_{-1}=\mathrm{id}_R-\mathrm{id}_R=0$. Below $-1$ all source modules vanish. Passing to the quotients proves the identity in all remaining degrees. If $P$ is empty, only the degree $-1$ check is needed; if $Q$ is empty, the assumed maps force $P$ empty. Thus no nonemptiness assumption has entered the proof.

## Unfinished work

The two new lemmas are deliberately unsplit and available for parallel work as required by the return. The parent split is complete at this level. Required server checks and direct delivery are recorded after they run.

## Verification and preflight repair

Ran the sandbox's small_cases.py on every labelled partial order with 0 through 3 elements, every weak tuple of length 0 through 4, and all monotone maps and comparable pairs among them. All 532 normalization, 105858 entrywise-map and 418032 prism checks passed over integer coefficients, including d squared, compatibility of q with deletion, preservation of D by d and maps, and the weak prism identity and preservation of D. This checks the sign and indexing examples without claiming a Lean proof. Empty tuples/posets, constant and collapsing maps, equal endpoints, and f=g are included. The symbolic arguments also use only addition and signs, hence introduce no coefficient-ring restriction.

First dry run exited with one failure: the weak-prism child had no bracketed node citation, despite spelling out its data inline. Repaired by explicitly citing the existing integer-degree module-chain-complex definition for the direction of the differential, and adding exactly that statement dependency. No new mathematical hypothesis or result was added. Local JSON checks found only proof, proof_deps and split_report changed on the parent; its statement and all maintainer fields agree with the current read repository. Every citation quote is a literal substring of its final child statement.


## Repair of the landing refusal at f03bec3a764

The 2026-10-22 06:44 UTC return approved the mathematics but refused landing because a side-DAG completion had not been promoted to the live queue. I continued the retained sandbox rather than recreating its work. The required first dry run finished successfully at 550d5d43d06. I then compared all three delivered node files with the current read repository: neither child exists there, and the parent differs only in proof, proof_deps and split_report. Its statement, statement dependencies, blueprint provenance, Lean records and maintainer metadata match. I rebuilt the parent from that current node, applying only those three split fields; the delivery tool supplies the new current-base commit.

I re-read the released stage-1 repair note, which explicitly reopens this item despite its split status and requires two independent statement-only children. I also re-read the current statements of def-sfb-augmented-poset-chains and def-weil-pbc-module-chain-complex-homology. The former uses strictly ordered lists with finite-support coefficients and a unique empty basis vector in degree -1; the latter uses integer degrees and differentials from n to n-1. These are exactly the modules, augmentation and differential direction in both children. No changed definition requires a mathematical adjustment. The original eight-step argument remains verbatim above, allocated to the same two comparably sized children.

For the three parent steps I reopened both child statements. Step 1 takes the surjective chain map, its kernel and induced chain isomorphism from normalization. Step 2 takes its entrywise chain-map assertion, preservation of D, identity/composition equations and explicit quotient generator rule. Step 3 takes that quotient rule and surjectivity together with the weak-prism statement's preservation of D and equality in every integer degree. The citation record previously included irrelevant functoriality quotations for steps 1 and 3 and did not quote step 2's entrywise and quotient clauses; I replaced those with the exact clauses just checked. The maps descend because they preserve D, and applying q followed by cancellation of its surjective components gives the final equality, as written in the parent.

I re-read Stacks simplicial.tex at equation-homotopy-to-homotopy and lemma-homotopy-s-N (Tag 019S), checking the cancellation argument and the sign reversal needed for g-f. I rechecked the existing Mathlib search results and read the generic alternating-face-map construction and toChainHomotopy formula: they still require extra poset, normalization and augmentation constructions and are not one-line matches. The questions and statements have not changed, so the actual recorded searches and their unavailable-service verdict remain intact. A fresh project-source search found no attachment; the live Sheaf prism module still has sorry for map_comm, map_id, map_comp and prism_identity. A fresh whole-DAG search found no new weak-chain lemma and no new same-tag pair beyond those already distinguished in Not duplicates.

This rebase review checks the actual current cited definitions and retained child statements, including finite-poset and monotonicity hypotheses, f<=g, empty posets, the zero coefficient ring and all negative degrees. No statement is changed, no Lean is written, and no compilation is run. The final dry run and push follow this updated report.

## Current-base repair after the repeated landing refusal

I continued the retained three-node sandbox, citation file, original eight-step argument and actual search log; the ready record from the preceding attempt names head 6f33112c08e. The required first dry run exited with a new duplicate-tag diagnostic, before preflight: lem-sfb-equivariant-continuous-cochain-prism now also cites 019S. I opened its entire statement. Its objects are continuous equivariant function cochains on a topological group over a topological field; its operator lowers nonnegative cochain degree and sums over a permuted finite family of self-maps. Neither the quotient of weak poset chains over an arbitrary commutative ring nor preservation of repeated tuples and integer augmentation occurs in that statement. The two new pairwise distinctions are now recorded under Not duplicates. This supersedes the previous attempt's observation that no further same-tag pair had appeared.

For rebasing I compared every field of the sandbox parent against the current read DAG, then rebuilt it from that current node with only proof, proof_deps and split_report overlaid. All inherited statement, statement dependencies, source, provenance, Lean attachment and maintainer review metadata agree. Neither child exists in the current DAG. I re-read both live definition statements, both retained child statements, the released repair note and the Stacks cancellation calculation at simplicial.tex lines 4739–4846. The live definitions still use finite-support strict lists, the empty generator in degree -1 and differentials n to n-1; no hypothesis or definition has changed the meaning of the split. The fresh project-source search finds no complete attachment; the recorded Sheaf map_comm, map_id, map_comp and prism_identity proofs still contain sorry.

The three assembly steps still use exactly the statements quoted in citations.json: normalization provides the quotient chain isomorphism and surjective chain map in step 1; its entrywise maps, repeated-tuple preservation, generator formula and identity/composition equations give step 2; its quotient map and the weak-prism child's explicit H and dH+Hd equation give step 3. I made the degree -1 assembly explicit in step 3: both homotopy terms vanish and both induced maps fix the empty generator, hence their difference is zero. Below -1 the source vanishes. This also checks the empty-poset case without adding a nonemptiness hypothesis. The comparable-map and commutative-ring hypotheses needed by the weak prism are exactly those supplied by the unchanged parent.

I read the retained searches.jsonl and every new-node search record, including the unavailable LeanSearch verdict, and re-opened the generic Mathlib alternating-face-map, simplicial-homotopy and nondegenerate-chain sources. Their inputs still require a separate poset simplicial model and quotient/augmentation comparison. The statements and search questions have not changed, so no search is fabricated or repeated. The children remain statement-only, independent of the parent and of each other; the complete old arguments remain allocated to them above as required by the human re-split order. The assembly remains under 3000 characters, with no step over 2000 characters. The final current-base dry run and direct push follow this repair.


## Repair of the 2026-10-23 promotion return

The new return again approves the reader's work but refuses landing because the side completion has not been promoted to the live queue. I retained the sandbox rather than discarding any proof, source, search or citation. Its previous durable receipt names c3d45c7d037; the node and report fingerprints in that receipt match the retained inputs at the start of this retry. The required initial dry run completed successfully at 6cf68a628d8. This is only a preflight result, not a claim that the earlier delivery landed.

I compared all three node files against the current read repository. Neither child is present, and the parent differs only in proof, proof_deps and split_report. I reconstructed the parent from that current record and overlaid those three fields, preserving its statement, statement dependencies, provenance, Lean record and all maintainer metadata. The released stage-1 repair order still explicitly reopens the eight-step proof and requires two independent statement-only children of comparable size. The earlier positive review therefore does not override that order. The delivery tool rebases the resulting commit onto the freshly fetched live branch.

I reopened both current definition statements and both retained child statements. The normalization lemma still asserts a surjective chain map with kernel D, the induced chain isomorphism, entrywise chain maps preserving D, their identity/composition laws and their explicit quotient generator rule. These are precisely the assertions used in steps 1 and 2. In step 3 the weak-prism child still supplies the operator on the same weak tuples, preservation of D and the equality in every integer degree. I expanded the assembly to display q_(Q,n+1) H_n = h_n q_(P,n), the entrywise-map compatibility and the resulting equality after applying q_(Q,n); cancellation uses the normalization child's asserted surjectivity. Thus the repair adds a degree-checked descent calculation instead of re-pushing the unchanged split. Every quoted sentence in citations.json remains verbatim, and every cited parent-step/node pair is covered.

The two definition statements still use integer degrees, alternating deletion, finite-support strict-chain modules and the fixed empty generator. The child hypotheses are a commutative ring and finite partial orders; the prism additionally assumes monotone f,g and pointwise f<=g, exactly as the parent supplies. Repetitions remain repeated under entrywise maps; their prism images remain in D. For degree -1 both homotopy operators vanish and both induced maps are the identity. For lower degrees the source vanishes. The empty-poset and zero-ring cases therefore introduce no extra hypotheses. Both children remain independent statement-only nodes, and all eight original calculations remain verbatim in the preserved-argument section.

For sources I re-read Stacks simplicial.tex, equation-homotopy-to-homotopy and lemma-homotopy-s-N, Tag 019S, lines 4739–4846, including the double-sum cancellation and opposite signed convention. I also read the current literature/blueprint/latest direct-images proof, paragraph (3), and its unit statement, from the snapshot recorded as main-20261023-1620 (7284bb09daf97437d544c51882b325f9c52cd345). The generic combinatorial input is still below that open-direct-image route and does not replace a chapter or unit argument. Fresh blueprint searches for weak tuple and prism return zero matches; the ancestor remains null, as in the inherited provenance.

A fresh whole-project WeilConjectures source search gives no matching attachment; the existing Sheaf prism module still has sorry for map_comm, map_id, map_comp and prism_identity. A fresh same-tag DAG search introduces no further pair beyond those distinguished under Not duplicates. I read all retained new-node search results and their source candidates in AlternatingFaceMapComplex.lean, SimplicialObject/ChainHomotopy.lean and SimplicialSet/Homology/Nondegenerate.lean. They still require the extra poset model, quotient comparison and augmentation, so neither child is a one-line Mathlib leaf. The children's statements and search questions are unchanged; every recorded new-node search matches searches.jsonl and the unavailable service remains recorded unavailable. Inherited parent searches were made before this sandbox and are retained as history, not claimed as new calls in this retry.

This is my current-base review under the Review by Q137 signature above: B is checked by self-contained statement-only children, precise source labels and real searches; C by the opened statements and verbatim citations; D by the two separate retained raw weak-chain arguments and the explicit strict-chain assembly; E by the matching hypotheses and degree, repetition, sign and empty cases just checked. No step exceeds 2000 characters and the assembly is below 3000. No statement is weakened, no Lean file is changed and no compiler is run. The final server dry run and direct push follow this report update.
