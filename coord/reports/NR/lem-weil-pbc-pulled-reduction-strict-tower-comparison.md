# NR stage-1 delivery: lem-weil-pbc-pulled-reduction-strict-tower-comparison

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-pulled-reduction-strict-tower-comparison.json`: statement node, now split into nine proof steps; not a Mathlib leaf. Statement and existing metadata retained, with the precise blueprint provenance filled and actual new searches appended.
- `citations.json`: one verbatim statement quote per step/node citation.
- New nodes: 0. Mathlib leaves: 0. No unit or chapter files changed; no Lean written or compiled.

## Attachments

None. Searched `lean/WeilConjectures/` for the item's blueprint tag and for strict towers, completedPullback, pulledReduction, and reductionTower/pullback combinations. There is no declaration giving this entire augmented strict-tower comparison. The pre-existing flat common-quotient tower declaration under `lean/Sheaf/Paper/FlatCommonQuotientReductionTower.lean` covers a different existing dependency, not the item.

## WANTED

None. The needed Stacks sources and current blueprint text are present locally.

## Audit of the imported item

The statement was not changed. There was no proof in the imported item. The current blueprint ancestor is `lemma-weil-pbc-completed-pullback-reduction`, proof paragraph 2 in `literature/blueprint/main-20261015/blueprint/sec-proper-base-change/sk-prop-pbc-complete/lemma-weil-pbc-completed-pullback-reduction.proof.md`. Its sentence identifying the pulled-back reduction tower requires compatible representatives, and does not by itself justify augmentation or evaluation compatibility. The new proof supplies these details. The ancestor's first paragraph and its finite reduction/completeness conclusions are not asserted by this item and are not used to prove it.

I read `dag/chapters/sec-proper-base-change.json` and `dag/units/sk-thm-properbasechange.json`. The proof remains below the existing completed-pullback reduction step; it changes no unit or chapter route. Generic off-unit inputs are declared in `split_report.tool_uses` with individual reasons.

No dependencies of the statement were removed. Every proof dependency is an existing node; dependencies of those nodes were also checked for a path back to this item, and none was found. The existing sibling `lem-weil-pbc-pulled-reduction-normalization-comparison` depends on this item, so it is not used here.

## Mathlib and blueprint searches

The original item's recorded searches were preserved. New searches were run only through `batch2/msearch.py`, and their results were read before recording verdicts. Queries and summaries are in the item and the command's `searches.jsonl`:

- LeanFinder: augmented derived inverse image/reduction tower with limit projections; results were ordinary adic/perfectoid scalar-evaluation identities.
- Loogle: `"SheafOfModules", "pullback"`; results were underived presheaf pullback and pullback composition declarations.
- Grep: derived tower/pullback or restrictScalars/limit; no hits.
- LeanSearch: derived tensor quotient tower/pullback/augmentation; results were module tensor-quotient equivalences and ordinary sheaf pullback adjunctions.
- A second LeanFinder phrasing using exact inverse image and quotient units returned ordinary adic-completion transition/exactness statements and the Profinite Nobeling argument.

These do not give the derived augmented strict tower, its two coefficient presentations, and the normalized limit projections. The item is not a Mathlib leaf.

Ran `tools/blueprint_refs.py ancestor` on the item and searched the entire blueprint index for `pullback tensor`, `common quotient`, `strict reduction`, `reduction pullback`, and `augmented strict`. The matches were general projection/tower/completion statements, not this same assertion. `same_as` remains empty. Since there are no new nodes, no duplicate-tag pairs arise.

## Not duplicates

No new nodes. The proof reuses, in particular, `lem-weil-pbc-flat-common-quotient-reduction-tower`, `lem-weil-pbc-diagram-kflat-replacements`, `lem-weil-pbc-flat-scalar-restriction-kflat`, and `lem-weil-pbc-ringed-strict-tower-homotopy-limit` instead of creating their specializations.

## Review by NR

I read the item source, Stacks `proetale.tex`, Tag 099N (`lemma-pushforward-Noetherian-case`), especially its proof of (5), and the full current blueprint ancestor statement and proof. Stacks uses constant coefficient pullback commuting with derived tensor. Our item additionally distinguishes the completed ring sheaf from the constant one; I checked its existing flatness/quotient input against `sites-modules.tex`, Tag 093M (`lemma-completion-flat`). I read `sites-cohomology.tex` Tags 06YS (`lemma-K-flat-resolution`), 0G7E (`lemma-pullback-K-flat`), 06YY (`lemma-derived-base-change`), 07A2 (`lemma-tensor-product-K-flat`), 07A4 (`lemma-pullback-tensor-product`), and 0940/0941 (`section-derived-limits`, `lemma-derived-limit-is-ok`); also `sites-modules.tex` Tag 03EL (`lemma-tensor-product-pullback`) and `derived.tex` Tag 08BJ (`lemma-adjoint-preserve-K-injectives`). The augmented-index and unit calculations are my expansion of these local sources, so `proof_origin.by` is `agent`. No SGA source is used.

For each proof step I opened all cited node files and read their statements, not their proof paragraphs as a substitute for the statements. In particular:

1. The constant-completion equivalence states flatness and the common finite quotients without assuming the object complete for its finite-reduction comparison. The constant-left-module inverse-image node gives constant-ring identification and exactness for arbitrary rings, including the infinite ring A; the finite-coefficient exactness proposition alone would not suffice here. Diagram replacement applies to the one-object small category. Flat scalar restriction explicitly preserves K-flatness and flat terms, and the ringed pullback lemma explicitly has no flatness assumption on the structural ring map. Thus M represents N and Q is K-flat over C = g^{-1}B, while C is not identified with B'.

2. The adic datum states the actual strict tower on P, including its finite-coefficient normalization. The flat common-quotient node states an isomorphism of strict complexes, preserving the quotient cone; it supplies more than unrelated isomorphisms of derived levels. Cochain pullback tensor coherence supplies the chain tensor comparison. Finite exact pullback identifies UF_n with the derived finite pullback, and K-flat pullback shows this model is K-flat over the finite coefficient ring. I do not treat these reductions as K-flat over the ambient completed or constant ring.

3. Diagram replacement applies to the explicitly given countable augmented category, with one source object and the quotient arrows. Its statement gives actual strict replacement maps, not only separate levelwise choices. K-flatness of Res P makes the tensor of this replacement with P a quasi-isomorphism. Scalar-extension preservation and total-tensor closure, both explicitly stated by their cited nodes for unbounded complexes with flat terms, put every E_j in the B resolving class. Thus the augmentation is resolved together with its tower. This is an application of existing generic results, not a new augmentation-lifting axiom.

4. Cochain tensor coherence gives the displayed Z_j by balancing. The augmentations V_j' to the constant source/finite quotient complexes are quasi-isomorphisms because ordinary inverse image is exact. Tensoring them with D preserves this property by D's flatness over R'; the common-quotient formula identifies the resulting finite target with S_n'. Tensoring next with the K-flat C-complex Q preserves the quasi-isomorphism, even though C to D was not assumed flat. The resulting maps are one strict augmented map. This checks the subtle point that evaluation isomorphisms alone would not identify a strict derived diagram. The definition of completed pullback states its resolving-class computation, which applies to the E_j just constructed.

5. The ringed tensor section-calculus node defines sheafified pure tensors, their naturality, and the scalar-insertion unit. The two transition composites and the two augmentation composites are written explicitly on these generators. This step is elementary because the chain comparison maps were already constructed in steps 2–4. It identifies the specified finite composite, rather than selecting an arbitrary isomorphism with the same source and target.

6. Diagram replacement states quasi-isomorphism invariance for pullback on the resolving class; the adic datum states it for the strict reduction construction. The resolving-class node has its universal left-derived natural transformation and its computation on the class. Hence the natural chain maps, and their equalities, descend to the derived functors and do not depend on the chosen P or augmented V. The calculation for f(x) tensor s verifies naturality before this descent.

7. The restriction definition leaves the underlying abelian sheaf unchanged; exactness follows. The ordinary scalar adjunction node states extension is left adjoint to restriction, and flatness from the constant-completion node makes this left adjoint exact. Tower exactness is levelwise by its cited statement. Tag 08BJ's node then applies to these tower categories and this exact left adjoint, not to an arbitrary right adjoint. The strict derived-limit node explicitly computes total Rlim by K-injective tower resolution. Restriction therefore uses the very same tower resolution and the same component projections, proving the limit comparison without assuming exact products.

8. The derived-limit node supplies a functor, so applying it to tau and taking its inverse gives rho. Its natural evaluation triangle/projections, or equivalently projections on its K-injective model, give the stated equality in the indicated direction. I checked the types: rho goes from restricted Rlim H to Rlim R(N), and Res(p_n^H) equals tau_n p_n rho. This is composition with an invertible functorial map, so no new comparison lemma is hidden in this elementary step.

9. The completed-pullback definition explicitly constructs its augmentation by a map into a tower K-injective resolution followed by factorization through the limit. The strict derived-limit statement supplies the same computation. Step 5 identifies the actual compatible component chain maps after scalar insertion; the shared restricted resolution and Rlim(tau) carry their factorizations to each other. Projecting gives exactly the finite scalar-extension unit. This compares actual constructed maps and does not assert uniqueness merely from their components in a triangulated category.

I checked the hypotheses and edge cases: all sites and all indexing categories used here are small in the fixed coefficient universes; the augmented category is countable. The argument allows unbounded K and never uses derived completeness. It allows the identity g, where the remaining comparison is the common-quotient one, and K = 0, where every map is the zero-object identity. For I = 0 the tower is constant and the construction gives the ordinary identity scalar-comparison; for I = A all finite quotients and completed coefficient rings vanish, so K is necessarily zero. No finite type, properness, or flatness of g is used. No identification of completed and constant ambient derived categories occurs.

The checklist B–E is satisfied with no new statement-only nodes to audit: all notions remain in the existing statement dependencies; TeX is written once; source labels and Stacks tags are named; the proof contains the argument rather than moving clauses to new nodes; the only elementary steps are explicit tensor/unit identities, composition of isomorphisms, and factorization through a specified termwise limit. All steps are under 2000 characters. No statement dispute or source correction was necessary. The main corrections to the informal blueprint inference are the augmented strict replacement and the exact-left-adjoint justification for restriction preserving derived limits.

## Unfinished work and validation

No unfinished mathematical subclaim was introduced. Existing nonclosed dependencies remain existing DAG work; this delivery does not claim their Lean proofs. Server `review_split` passed with 0 new nodes. The required `deliver.py --no-push` completed successfully: `OK (not pushed)` at `751139e8166`, preflight passed. Local read-only data checks confirmed the statement is unchanged, all 33 quotes are verbatim in their cited statements, proof dependencies are exactly the union of step uses, and the longest step is 1272 characters. The authorized direct-delivery push follows this successful dry run.
