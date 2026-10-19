# Worker report: lem-coef-nondegenerate-simplex-face-poset

## Files written

- `dag/nodes/sec-six-functors/lem-coef-nondegenerate-simplex-face-poset.json`: statement, now split into six proof steps. No full Mathlib match; the universal factorization still requires the explicit section argument.
- `citations.json`: a verbatim statement excerpt for every citation of every proof step.
- `searches.jsonl`: actual outputs recorded by the required search wrapper. The item's inherited searches are retained; six fresh searches cover LeanFinder (two formulations), LeanSearch, Loogle and source grep (two queries).
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The proof reuses two existing Mathlib leaves.

## Attachments

None. Searched the entire read-only `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id, its blueprint tag, nondegenerate/nonDegenerate, nonsingular, and face-poset terminology. No matching project declaration exists. Mathlib declarations are partial interfaces, not project attachments. No compiler or Lean/Lake tool was run.

## Wanted sources

WANTED: Jacob Lurie, Higher Topos Theory, Variants 4.2.3.15 (5) and 4.2.3.16, printed p. 256, for lem-coef-nondegenerate-simplex-face-poset. The PDF was read online at https://people.math.harvard.edu/~lurie/papers/HTT.pdf (zero-based PDF page 273), but there is no local archival copy. The explicit proof is therefore marked `proof_origin.by = agent`, not represented as a proof copied from local literature. No download or literature-tree write was made.

## Corrections and searches

The item statement is unchanged. Its original source mentioned only Variant 4.2.3.15 (5); Variant 4.2.3.16 explicitly supplies this item's general hypothesis on monomorphic nondegenerate simplices, so the source reference now includes it. The six steps fill the originally empty proof. No statement dispute was found. No unit or chapter record was edited.

Read `dag/chapters/sec-six-functors.json`, `dag/units/sk-prop-sf-biduality-general.json`, the archived unit text, the item's historical blueprint ancestry, and the current archived `main-20261015/.../sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. The intervening finite-adjunction, accessible-Ind and cofinal-poset nodes explain why this combinatorial tool occurs below the ancestor. This delivery fills the nondegenerate-simplex step of the existing poset replacement and does not replace any unit argument.

Whole-DAG searches for monotone maps, nondegenerate simplices and face posets located the existing nondegenerate-decomposition and adjacent-collapse leaves; these were opened and reused. `tools/blueprint_refs.py ancestor` identifies `prop-coef-integral-exceptional-adjoint`; `search` was run for `nondegenerate`, `simplex`, and `face poset` across all imported blueprint nodes. No imported node duplicates this statement; `same_as` stays empty. The related `lem-coef-nondegenerate-simplex-comma-initial` is a consequence of this factorization, and `lem-coef-subdivision-face-poset-calculus` concerns subdivision, not this universal arrow. Neither is used, avoiding a circular or unrelated citation.

Read the returned Mathlib sources: `Nonsingular.lean`, including `SSet.Nonsingular.injective_map` and `SSet.N.existsUnique_of_le`; `NonDegenerateSimplices.lean`, including its partial order and `SSet.S.existsUnique_toNπ`; and `SimplexCategory/Basic.lean` at `eq_σ_comp_of_not_injective'`. The first two sources prove thinness/order or uniqueness of the surjective core map. Their statements do not give factorization of every arrow from an arbitrary simplex to any nondegenerate target through the core map. Hence the full item is not a leaf. No search was inferred from source reading: each fresh recorded query is in the wrapper log, with the actual tool name and query text. Inherited searches and verdicts were preserved as prior evidence.

## Unfinished work

None for this one-level split. HTT archival availability is the only source request; its missing local copy is reflected in the agent proof origin. The result makes no claim about cofinality or comma-nerve contractibility, which belong to the existing downstream items.

## Review by Q120

I checked the item against HTT printed p. 256, both the nondegenerate-simplex step (5) of Variant 4.2.3.15 and the general embedded-simplex paragraph of Variant 4.2.3.16. The general formulation does not assume that X is a nerve, finite, Kan, or globally determined by its vertices. The only cancellation used is inside a specified nondegenerate target, whose vertex map is injective by the item's hypothesis. This matters because distinct embedded simplices can have the same vertices in X: the proof never identifies such simplices just from their vertex sets.

Step 1 cites `def-cbc-enhanced-diagrams-cones`, whose statement explicitly describes standard simplices as monotone maps with precomposition operators. Evaluating the arrow equations at vertices and applying the assumed injectivity of the fixed target vertex map proves equality of operators pointwise. This is an elementary calculation, not an appeal to a definition node for a thinness theorem.

Step 2 cites that definition and `lem-weil-pbc-simplex-degeneracy-factorization`. I read its complete statement: for a monotone map constant at consecutive indices it supplies precisely a factorization through the elementary surjection collapsing those indices. The parameters here are k=n, its target ordinal parameter is m, and 0 <= i < n. Noninjectivity and monotonicity give the required adjacent equality. Composing the factorization with tau exhibits a forbidden degeneracy of sigma, with no assumption on tau needed for this part. The n=0 case is treated separately. The existing leaf records Mathlib's `SimplexCategory.eq_σ_comp_of_not_injective'` at Basic.lean:732, and I read that declaration rather than taking more from its proof. Its local Stacks sources are Definition 0165 (`definition-face-degeneracy`) and the factorization in the proof of 017K (`lemma-exists-hom-0-from-simplicial-set-finite`). No new node is needed for this fact.

Step 3 uses the arrows and injections proved in the preceding steps. Reflexivity and transitivity are identity and composition. Antisymmetry uses both dimension inequalities and explicitly shows that a monotone injection of [n] into itself is the identity. Therefore the equality is of actual objects with the same dimension and map, not just an assertion that a thin category is automatically a poset. These finite-order calculations are elementary and use no uncited structure theorem.

Step 4 cites `lem-weil-pbc-simplicial-set-nondegenerate-decomposition` and the standard-simplex definition. I opened that leaf's statement and read Stacks `simplicial.tex`, Lemma 017R (`lemma-splitting-simplicial-sets`), together with the preceding disjoint-union splitting formula. It supplies the unique dimension, surjection and nondegenerate simplex used here, with no finiteness or nonsingularity assumption. The proof step writes the maps represented by the top simplices explicitly and checks them by naturality, so no unrecorded Yoneda theorem is invoked. Its nondegeneracy convention agrees here: a monotone map from [n] to a smaller ordinal must repeat adjacent values and hence factors through an elementary surjection, as in step 2. The resulting bar-sigma is an object of B_X, as required.

Step 5 cites only the standard-simplex definition and uses the fixed decomposition from step 4. I checked that choosing the least element of every fibre is legitimate because s is surjective between nonempty finite ordinals; fibres are ordered, so the chosen section is monotone. The proof writes s a = id, t = alpha a, the vertex-level cancellation proving alpha constant on s-fibres, and the full equality tau Delta(t) = bar-sigma by composition with a. This supplies the comparison itself; no phrase such as 'transport' hides a lemma. The cancellation uses exactly the assumed monicity of the nondegenerate tau, and is not asserted for an arbitrary degenerate target.

Step 6 writes uniqueness by evaluating any proposed t' at s(a(j)). It also notes that t is an injective operator by step 2, since both its source and target are now nondegenerate. It uses only the explicitly constructed section and earlier conclusions, with no fresh external fact.

I checked sections B--E of delivery-errors against these files. There are no new statement-only nodes to have missing hypotheses, incomplete source tags or duplicate clauses. Every non-elementary input is one of the opened existing Mathlib leaves. Every `uses` entry has the quoted part of its statement in `citations.json`; `proof_deps` is exactly their union. The adjacent-collapse node is an existing leaf, so it is permitted across units without a new tool-use declaration. The other external citation is a definition. No circular dependency or replacement by an item's own clause was introduced. All six steps are shorter than 2000 characters, and the section/factorization argument is written as explicit equalities.

Small cases checked: X empty gives an empty poset and no factorization obligations; a vertex has n=r=0 and section id; a degenerate simplex over a vertex has constant s and t; a nondegenerate input has s=id; equal-dimensional arrows in both directions force identity, including dimension zero. For standard simplices I exhaustively checked the section and reconstruction identities for 1590 combinations of finite monotone maps with n,m <= 4 and r <= 3. These are checks of the mathematical formulas, not Lean builds. Dropping the monicity hypothesis is invalid: in the simplicial circle Delta^1/boundary, its single vertex has two different arrows to the nondegenerate loop, one for each endpoint. The proof therefore retains exactly the hypothesis needed for thinness and vertex cancellation.

No correction of the statement or new lemma was necessary. The substantive changes are the complete six-step proof and the more precise source reference; all historical creation, unit and blueprint fields are retained.
