# Repair report: lem-trf-frobenius-pullback-comparison-coherence

## Files written

- dag/nodes/sec-trace-formula/lem-trf-frobenius-pullback-comparison-coherence.json: unchanged statement, short assembly proof.
- dag/nodes/sec-trace-formula/lem-trf-positive-functor-binary-comparison.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-positive-functor-refinement-independence.json: statement, unsplit; no Mathlib match.
- citations.json, with a verbatim statement quotation for every proof citation.

## Attachments

None. The project source search found no exact finished declaration under lean/WeilConjectures. The recorded theorem WeilConjectures.TraceFormulaCoefficientConventions.frobenius_pullback_comparison_coherence in lean/Sheaf/Paper/FrobeniusPullbackComparisonCoherence.lean still has a sorry proof. Its definitions and docstring agree with the positive-index recursion, and its two binary equations encode the two orders of refinement. No Lean was edited or compiled.

## WANTED

None. The blueprint source and local Stacks source used in the retained normalization are available. The two generic categorical arguments are agent expansions of the blueprint iterate assertion, not claims that Stacks 0D6D itself states tree coherence.

## What was wrong and what changed

The 2026-10-22 human re-split return identifies a 4135-character proof that concentrated too much work in one item. The sandbox contained only dispatcher markers, no retained node, report, or search log. I therefore copied the current read-only repository node, including all its metadata and past search records, and repaired its split-owned fields. No statement, chapter, unit, route, or existing dependency node was changed. The new proof has five steps and two independently reusable generic inputs. Both new inputs are status unsplit, have empty proof and proof_deps, and have no proof sketch inside their statements.

The binary-comparison node carries all of old steps 3 and 4 (1254 characters of argument): existence/naturality/invertibility by recursive composition, followed by induction on the first summand using the triple cocycle. The refinement-independence node carries all of old step 5 (1064 characters): weighted tree induction, interchange of branch refinement by naturality, deeper-context interchange, multiway partitions, and canonical reassociation. They are comparable separate arguments. The original coefficient setup, canonical associator computation, triple cocycle, and final inverse/cancellation computation stay in the parent. The complete original argument is preserved below, not replaced with a shorter unrecorded summary.

## Not duplicates

- lem-trf-positive-functor-binary-comparison vs lem-trf-frobenius-pullback-comparison-coherence: generic binary multiplicativity from a triple-cocycle hypothesis, without geometry, tree independence or the final inverse identity; it discharges the induction needed by the parent.
- lem-trf-positive-functor-refinement-independence vs lem-trf-frobenius-pullback-comparison-coherence: a generic tree-evaluation criterion assuming a supplied binary-compatible family d, rather than deriving that compatibility for canonical geometric pullbacks or proving the inverse identity.
- lem-trf-positive-functor-binary-comparison vs lem-trf-positive-functor-refinement-independence: the first constructs d and proves binary compatibility from a cocycle; the second assumes that compatibility and proves independence for all finite tree evaluations and refinement orders. Neither assumes the other conclusion.
- lem-trf-positive-functor-binary-comparison vs lem-trf-derived-pullback-coherence: the existing node supplies the geometric triple cocycle only; it does not construct d or prove binary compatibility.
- lem-trf-positive-functor-refinement-independence vs lem-trf-derived-pullback-coherence: triple coherence is not a theorem about all finite weighted trees with independently supplied binary-compatible d.
- lem-trf-positive-functor-binary-comparison vs def-trf-frobenius-pullback-power-comparison: the existing definition introduces geometric P,C,d but asserts no coherence; the new node is the abstract binary theorem.
- lem-trf-positive-functor-refinement-independence vs def-trf-frobenius-pullback-power-comparison: a definition of comparisons is not the tree-evaluation theorem.

Whole-DAG searches used binary tree, binary splitting, splitting tree, positive endofunctor, family of endofunctors, and coherence/comparison with endofunctor. Whole-blueprint searches used functor power, binary tree, binary comparison, refinement order and endofunctor. Existing natural transport, global Frobenius iterate and endofunctor power nodes do not state either new theorem. Neither new source claims a Stacks tag: the generic arguments follow the expanded blueprint proof, whereas 0D6D remains attributed to the existing geometric comparison nodes.

## Mathlib search review

Each new node has its own five queries from searches.jsonl: LeanFinder with two phrasings, LeanSearch, Loogle, and grep. LeanSearch returned rate-limit errors and is honestly unavailable. The binary search found Equivalence.powNat (Equivalence.lean:512), which constructs powers of an equivalence but provides no comparison of a separate family P. Its other hits concern graded-object components, polynomial functors, and transfinite iterations. The refinement searches found whisker_exchange (Monoidal/Category.lean:324; Bicategory/Basic.lean:113) and FreeMonoidalCategory.subsingleton_hom (Monoidal/Free/Coherence.lean:314), as well as unrelated ordered partitions. I read the relevant local source. Whisker exchange is one naturality interchange, not the full weighted-tree induction. Free monoidal thinness covers formal associators/unitors, not the arbitrary supplied C maps indexed by positive weights; using it here requires an additional construction/argument. Endofunctor monoidal structure (Monoidal/End.lean:45) confirms identity associator components. No hit states either full result or specializes to it in one line. The existing item search records were retained rather than rerun without a changed question.

## Review by N7

I read the current blueprint proof of lem-trf-frobenius-operator-compact-description, the recorded chapter and sk-d-weil unit, the six returned proof steps, and the current Lean theorem/docstring. For the geometric comparison I read Stacks sites-cohomology.tex, lemma-derived-pullback-composition (Tag 0D6D), including its flat-term K-flat computation. The new nodes' source is the explicit categorical expansion of this blueprint iterate assertion, and their full intended arguments are reproduced below. No SGA route is used.

Step 1 cites def-weil-pbc-proetale-operations precisely for ordinary uncompleted unbounded operations, def-weil-l-adic-coefficient-extension clause 4 for finiteness of A, lem-weil-pbc-proetale-derived-pullback-composition for canonical C with the required composite coefficient identification, and lem-trf-constant-coefficient-composition for equality of that identification with the canonical constant one. I opened each statement and copied the relevant text into citations.json. The ring is commutative as a quotient of the valuation ring, n is positive, and each power of g is a scheme endomorphism. The functor associator computation uses only its definition.

Step 2 cites lem-trf-derived-pullback-coherence, whose statement gives exactly the normalized triple comparison after the canonical associator. Substituting j=g^a, h=g^b, k=g^c gives the displayed cocycle; all three exponents are positive, the scheme is the same X, and the coefficient ring is the finite A from step 1. I checked the direction and that this invokes no arbitrary replacement comparisons.

Step 3 uses the full statement of lem-trf-positive-functor-binary-comparison: category D(X_proet,A), P_r=L(g^r)^*, T=P_1, the natural isomorphisms from step 1 and the cocycle from step 2 satisfy every hypothesis. This supplies the recursively constructed natural isomorphisms and binary equality, not just their existence. Step 4 uses the full statement of lem-trf-positive-functor-refinement-independence, with exactly those d and C and the binary equality of step 3. Its root-before-children orders model every legal splitting schedule; nested refinements are inside the same functor contexts and all target reassociations are canonical. Both citations have verbatim hypothesis/conclusion quotations.

Step 5 is elementary inversion of the displayed recursion followed by functoriality and cancellation, and uses no additional black-box fact. It gives b_r=C_(1,r)^(-1) with the correct source and target at every M. The two long original inductions have been removed from the parent and made explicit separate work items; none is now hidden in an elementary step. There are no parent steps above 2000 characters and the parent total is below 3000.

I tested the new binary statement at a=1, a=2, b=1, and with T and all P identities: the base is precisely the recursion; at a=2 the sole required cocycle is (1,1,b). For the tree statement I tested r=1 (identity), r=2 (one vertex), r=3 (the two bracketings), r=4 (independent branch refinements), and j=1. Naturality at d_b,M exchanges the two branch orders with correctly typed source P_a(P_b M) and target T^a(T^b M). Empty categories have no component obstruction; zero objects and empty schemes introduce no nonemptiness assumption. Positive weights exclude zero-child and empty-partition issues; r=1 is included explicitly. The statements require no small category of all trees or limits, so no hidden size hypothesis is introduced. The new nodes have only definition dependencies, so no route departure or cycle through the parent is created.

## Second reading by N7

This is my direct-delivery self-review, not a claim that a second worker read it. The dispatcher explicitly requires direct delivery. I checked delivery-errors B through E against each new statement and each retained step, retained all source/provenance fields of the existing item, and verified quotes and actual search logs.

## Original arguments and assignment to the new work items

### Returned step 1

Retained as parent step 1.

Work in the ordinary unbounded category $D(X_{\mathrm{proet}},A)$, with the operations of [def-weil-pbc-proetale-operations]. The coefficient ring $A=A_{E,n}$ is finite and commutative by clause 4 of [def-weil-l-adic-coefficient-extension]. Write $C_{a,b}=c_{g^a,g^b}:P_{a+b}\xrightarrow{\sim}P_aP_b$ for $a,b\geq1$. These are the natural isomorphisms of [lem-weil-pbc-proetale-derived-pullback-composition]. The canonical constant coefficient identification on a composite is the composite identification by [lem-trf-constant-coefficient-composition], so the comparison applies with exactly the coefficient maps of the item. We write composition of endofunctors in ordinary functional order. The canonical functor associator has identity components: both parenthesizations act by $F(G(H(M)))$ on objects and $F(G(H(u)))$ on morphisms. Thus all reassociations below are interpreted by those specified associators.

### Returned step 2

Retained as parent step 2.

Apply [lem-trf-derived-pullback-coherence] to $j=g^a$, $h=g^b$, $k=g^c$, all endomorphisms of $X$, with its finite commutative coefficient ring equal to $A$. Its normalized comparisons are exactly the $C$ of step 1. For all positive $a,b,c$ it gives the natural-transformation identity
$$P_a(C_{b,c})\circ C_{a,b+c}=(C_{a,b}P_c)\circ C_{a+b,c}:P_{a+b+c}\longrightarrow P_aP_bP_c.$$
Here $(C_{a,b}P_c)_M=C_{a,b,P_cM}$ and $P_a(C_{b,c})_M=P_a(C_{b,c,M})$. No change of coefficient category or choice of comparison is made.

### Returned step 3

Transferred to lem-trf-positive-functor-binary-comparison.

Define natural isomorphisms by induction on positive $r$:
$$d_1=\mathrm{id}_T,\qquad d_{r+1}=T(d_r)\circ C_{1,r}:P_{r+1}\longrightarrow T\circ T^r.$$
The base is well typed because $P_1=T$. Each successor is natural and invertible: functors preserve inverses, and composites of natural isomorphisms are natural isomorphisms. This is the comparison from repeatedly taking the first summand to be $1$. These assertions follow directly by composing the naturality squares and the inverse identities for the comparisons of [lem-weil-pbc-proetale-derived-pullback-composition].

### Returned step 4

Transferred to lem-trf-positive-functor-binary-comparison.

For every $a,b\geq1$, prove by induction on $a$ the equality
$$d_{a+b}=T^a(d_b)\circ(d_aP_b)\circ C_{a,b}. \tag{*}$$
At $a=1$, $d_1P_b$ is the identity, so this is the recursion of step 3. For $a\geq2$, the recursion and the induction hypothesis at $(a-1,b)$ give
$$d_{a+b}=T^a(d_b)\circ(T(d_{a-1})P_b)\circ T(C_{a-1,b})\circ C_{1,a-1+b}.$$
Use step 2 with $(1,a-1,b)$, valid because $a-1\geq1$, to replace its last two factors by $(C_{1,a-1}P_b)\circ C_{a,b}$. The middle factors then equal $d_aP_b$ by the recursion at $a-1$. This proves $(*)$ for every positive $a,b$. The calculation is an equality of natural transformations, so it also holds after evaluation on every complex.

### Returned step 5

Transferred to lem-trf-positive-functor-refinement-independence.

Any complete sequence of binary splittings of the positive integer $r$ has a finite ordered binary tree: a vertex of weight $a+b$ applies $C_{a,b}$, and its two children refine $a$ and $b$. Induct on $r$ to compare its map with $d_r$. A tree of weight $1$ has no splitting and gives $d_1$. At a root $(a,b)$, both weights are smaller than $r$, so the subtree maps are $d_a,d_b$. The resulting composite is the right side of $(*)$, hence $d_r$. Refining the second subtree before the first gives the same map, since naturality of $d_a$ at $d_{b,M}$ reads
$$T^a(d_{b,M})\circ d_{a,P_bM}=d_{a,T^bM}\circ P_a(d_{b,M}).$$
Splittings at distinct deeper vertices commute by this same naturality equation inside their common functor context. A splitting into $j$ positive summands is a binary refinement with $j$ leaves; the just-proved induction applies to any parenthesization. The associators in step 1 have identity components, so inserting their reassociations does not change these component maps. This proves the stated independence of both order and reassociation.

### Returned step 6

Retained as parent step 5.

Finally the recursion gives
$$d_{r+1,M}^{-1}=C_{1,r,M}^{-1}\circ T(d_{r,M}^{-1}).$$
Postcompose $T(d_{r,M})$ and use functoriality and the inverse law to obtain
$$d_{r+1,M}^{-1}\circ T(d_{r,M})=C_{1,r,M}^{-1}=b_{r,M}.$$
At $r=1$ this says $d_{2,M}^{-1}=C_{1,1,M}^{-1}$, consistently with $d_1=\mathrm{id}_T$. The argument applies to every object $M$ of the unbounded derived category.

## Unfinished work

The two new statements intentionally remain unsplit for independent workers, as ordered by the return. This stage does not change the existing Lean sorry. The prescribed deliver.py --no-push completed with exit 0 and printed OK at 52f98c44d58, with server preflight passed. After correcting two Mathlib source line references in this report, a final dry run precedes the authorized push. The final session output is the delivery receipt.
