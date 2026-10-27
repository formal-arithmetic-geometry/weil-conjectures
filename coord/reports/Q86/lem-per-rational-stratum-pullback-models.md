# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-rational-stratum-pullback-models.json`: statement, unchanged; now split into six proof steps. Mathlib verdict: no match for the full statement.
- No new nodes; zero Mathlib leaves. `citations.json` supplies the 18 step/node quotation records. `searches.jsonl` preserves the five searches actually performed in this sandbox.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint id and rational-stratum/pullback-model terminology, and read the nearby perverse-operations interface. No project declaration supplies this completed continuous-coefficient rational comparison with every clause. Ordinary finite-coefficient and geometric-point results do not attach this item.

## WANTED

None. The required Bhatt–Scholze PDF, current blueprint and Stacks sources are available locally.

## Issues found and changes

The imported item was statement-only. Its statement is sound and was retained verbatim. The comparison must be ambient on the arbitrary schemes U and U': imposing noetherianity there, or applying a constructible realization equivalence there, would not prove the statement. Likewise coefficient flatness is unnecessary because the source module on a trivializing chart is finite free. The proof spells out both points. The preliminary affine calculation preserves the scheme structure of S', rather than replacing the pullback by the inverse image as a reduced subvariety.

The existing normalized realization, composition and slice nodes already carry the substantial comparison results. The remaining basis-tensor isomorphism, K-flat verification for a finite free degree-zero complex, and local zero-section argument are short arguments from these interfaces and definitions. They therefore remain steps instead of new nodes. The item is not a Mathlib leaf: `SheafOfModules.pullbackObjFreeIso` (Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean:118, with basis compatibility at 125) gives ordinary free-sheaf pullback, whereas the item also compares the specified quotient-completed functor under realization and derived restriction on stratum charts.

## Not duplicates

No new node was created. The existing `lem-per-continuous-rational-derived-realization` gives the global realized pullback; `lem-per-continuous-coefficient-slice-normalization` supplies arbitrary-chart restriction; neither is copied into another node. Blueprint searches for rational pullback, finite free and slice restriction found no blueprint item stating this full chart calculation. The original blueprint ancestor and its place/via chain are preserved.

## Review by Q86

I read Bhatt–Scholze, Definition 6.8.1 and Lemma 6.8.2 (continuous coefficients), Definition 6.8.3 (lisse means locally finite free), Definitions 6.8.6 and 6.8.8 (constructible sheaves and complexes), and Remark 6.8.15 (ambient scalar-extension pullback and exact immersion restriction). I also read the current main-20261015 text of `lem-per-smooth-pullback-t-exact`, its chapter and Fourier-exactness unit, and the parent `lem-per-adic-stratified-pullback-texact`. This split supplies the ordinary-cohomology pullback calculation in that existing route, without changing the perverse unit or its targets.

For step 1 I read both immersion definition statements and the slice-normalization statement, including its exact ordinary inverse image and locally closed immersion clauses. The affine identity (R/I) tensor_R T = T/IT verifies that the pullback is the actual locally closed subscheme. Step 2 uses the *statement* of continuous rational derived realization: it explicitly carries the fraction extension of completed pullback to the displayed derived scalar-extension functor. Its noetherian, dimension and invertibility hypotheses are those imposed on X,Y in the item; K is allowed to be an arbitrary raw rational object with the chosen realization. No proof of a cited node is used as a hidden interface.

For step 3 I read `lem-sfb-ringed-derived-monoidal-comparisons` in full and Stacks sites-cohomology.tex, Tag 0D6D, label lemma-derived-pullback-composition. That node supplies canonical ambient composition and its compatibility with a geometric 2-isomorphism whose ring maps commute. The realization statement supplies precisely the finite-quotient normalized identity/composition comparisons; the slice statement gives exact immersion restrictions, identifying G_i(F[0]) with F|S[0]. Thus the two factorizations of the same map S' -> X have the required comparison, rather than an unrelated isomorphism between their outputs. Locally closed subschemes of the noetherian finite-dimensional ambient schemes retain these hypotheses; arbitrary charts are used only later in ambient categories.

For step 4 I checked the weakly etale base-change statement and Stacks more-morphisms.tex, Tag 094U, label lemma-base-change-weakly-etale (2). The slice-normalization statement explicitly treats any scheme and nonnoetherian site objects, continuous-function coefficients, and restriction of ambient pullback. Its conclusion is exactly the restriction taken in this step. No coefficient-ring isomorphism is asserted for the arbitrary map g_U; only the slice maps have such identifications.

For step 5 I read the flat-sheaf, K-flat-complex and sheaf-tensor definition statements and the generic derived-pullback statement, as well as Stacks sites-cohomology.tex, Tag 06YY, label lemma-derived-base-change. Tensor with a degree-zero finite free module is a finite sum of the input complex, so it preserves acyclicity and has flat terms directly. This verifies the two hypotheses of the quoted K-flat computation instead of assuming flatness of the structural coefficient map. I checked the balanced relation and the two composites of the explicit inverse on local pure tensors. The formulas respect restriction and hence sheafify. Naturality follows by applying the same scalar formula to a matrix representing a map in two trivializations; its entries are pulled back through the structural map. The comparison itself is the normalized ambient one from the earlier steps.

For step 6 I read the covering base-change statement and Stacks topologies.tex, Tag 022D, label lemma-fpqc (3), together with the definition of a pro-etale covering. The two cited stability statements jointly give a covering by valid site objects, not just a surjective family of arbitrary schemes. Exact slice restriction commutes with cohomology, so the displayed tensor calculation annihilates every nonzero-degree cohomology restriction. For every site object V, pulling back the cover and applying the sheaf's separatedness axiom then annihilates each section; this is the full local-to-global argument and needs no assertion about enough geometric points. The module-category definition really states that these objects are sheaves of abelian groups.

I tested rank 0, rank 1, identity g, empty S', and a general nonflat coefficient homomorphism: rank 1 gives the ordinary multiplication/unit inverse, rank 0 gives empty sums, and the calculation never tensors an exact sequence by a nonflat target coefficient ring. On the empty site the empty covering forces every module to be zero. No new statements need small-case testing. I checked delivery-errors B--E: no unsearched or duplicate node, no proof concealed in an unsplit statement, every non-elementary input is a cited statement with a literal quote, no renamed clause as a new lemma, no assertion that arbitrary inverse image preserves a completed coefficient ring, and no unverified flatness assumption. Each proof step is under 2000 characters. A dependency traversal of the proposed citations finds no path back to the item. Off-unit generic tools are declared only in split_report.tool_uses for maintainer review.

## Unfinished work

None at stage 1. No Lean was written or compiled. The first server dry run passed: `OK (not pushed)` at `119169a5cc0`. After that pass I expanded the citation quotations for realization, immersion restriction, arbitrary-chart restriction and normalized composition so each quote contains the exact clause used in its step. A final dry run checks this completed delivery before push.
