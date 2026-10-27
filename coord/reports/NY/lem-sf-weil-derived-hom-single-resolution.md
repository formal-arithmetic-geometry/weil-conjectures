# Stage-1 delivery: lem-sf-weil-derived-hom-single-resolution

## Files written

- `dag/nodes/sec-six-functors/lem-sf-weil-derived-hom-single-resolution.json`: statement node, now split into seven steps. Mathlib searches find no exact comparison. Statement and statement dependencies are unchanged.
- `citations.json`: eight step/node entries, each containing a verbatim excerpt of the cited statement.
- `report.md`: this report. `searches.jsonl` is the unedited search-command log.

No new nodes and no Mathlib leaves. No Lean was written or compiled. The shared repository and launcher were only read.

## Attachments

None for the item. The project-wide search for the item id returned no declaration. I read `WeilConjectures/WeilSheaf/DerivedHom.lean:111-113` and `CategoryTheory/DerivedCategory/BifunctorHom.lean:94-126`: these define the two-replacement functor; they do not prove precomposition by an arbitrary quasi-isomorphism is invertible. The BifunctorHom module explicitly warns that its construction alone does not imply this invariance. The singleFunctor comparison in `WeilSheaf/Fourier.lean:1237` addresses a different exact-functor computation, not the item.

The useful closed declaration `CategoryTheory.Endofunctor.IsoAlgebra.preservesKInjectiveComplexes_forget` occurs in `CategoryTheory/DerivedCategory/RightDerivedFunctor/IsoAlgebra.lean:64-65`; its proof uses the exact free left adjoint. I read that construction in `CategoryTheory/Endofunctor/IsoAlgebra.lean:98-177,173-201,315-341`. Rather than introduce a duplicate specialization of the existing exact-adjoint criterion, the item constructs that adjoint explicitly and cites `lem-weil-pbc-right-adjoint-preserves-kinjective`. No attachment to a new node is needed.

## WANTED

None. The argument uses the Stacks sources available in the repository, plus an explicit fixed-pair construction. It does not use SGA.

## Corrections and scope

No mathematical statement correction and no STATEMENT-DISPUTED claim. The statement is true for all the stated sheaves A; its bounded-below restriction on N is retained even though the proof does not use it. In particular, no lissity, finite rank, tensor-dual description or constructibility assumption was added.

The inherited blueprint reference had `from.node: null`. Its parent `lem-sf-weil-lisse-internal-hom-tensor-dual` now points to `lem-a1-local-boundary-duality`; I filled that same actual ancestor and kept the parent in `via`. I read the current main-20261015 local-boundary-duality statement and proof, including its opening lisse duality identity. I read the item's recorded unit `sk-prop-sf-rf-shriek-preservation` and chapter `sec-six-functors`; the present comparison is a foundation below an already imported node, and does not replace a unit or chapter proof step. The unit is not the statement of this item, so no unit record is changed.

The important gap to avoid was treating equivariant K-injectivity as ordinary K-injectivity without proof. Stacks 0A95 is applied only after the exact left adjoint to the forgetful functor is established and the existing 08BJ node is applied. Infinite products of sheaves are never assumed exact. There is no identification of the native derived category with fixed pairs in an ordinary derived category.

## Not duplicates

No new nodes. I searched the whole DAG and blueprint for K-injective, fixed-pair, induction and single-Hom statements and the source/library for the relevant declarations. The ordinary `lem-sc-derived-internal-hom-single-comparison` concerns modules on a scheme's structure sheaf, so it does not by itself prove this native equivariant assertion. `lem-sf-weil-native-closed-forgetful` imposes separated finite-type hypotheses absent here and bundles much more structure, so it is not used. The existing general 08BJ, 0A95, Grothendieck-module-sheaf and K-injective localization nodes suffice.

## Mathlib searches

I retained the item's inherited search records and ran two fresh natural-language phrasings for the item, Loogle, grep and LeanSearch through the required `msearch.py NY lem-sf-weil-derived-hom-single-resolution` command. Their exact query strings, actual hit summaries and verdicts are in `mathlib_searches` and `searches.jsonl`. I also searched the potentially needed fixed-pair K-injectivity foundation with two phrasings and the other three search kinds before deciding no new node was needed. All services answered. The hits concerned objectwise right-derived functors, ordinary global Hom complexes, homotopy invariance, or unrelated single-object formulas. None compares the product internal-Hom complex of two K-injective native Weil representatives with fixed-source right derivation. No search was invented or rewritten as a query that was not run.

## Review by NY

I read Stacks `sites-cohomology.tex`, Tag 0A95, label `lemma-RHom-well-defined`, with its preceding/following internal-Hom context. Its target complexes must be K-injective as ordinary module sheaves; its first-variable map may be an arbitrary quasi-isomorphism, with no flatness or boundedness hypothesis. I read `derived.tex`, Tag 08BJ, label `lemma-adjoint-preserve-K-injectives`: it requires an additive right adjoint with an exact additive left adjoint. I checked those assumptions rather than using equivariant K-injectivity alone. I also read Tag 070I's Hom-to-derived criterion underlying the choice comparison. There are no new nodes to audit against a separate source.

Step 1 uses the statement of `def-weil-endofunctor-fixed-pair-category`, which supplies exactly the intertwining equation and faithful forgetful functor. The additional elementary argument constructs kernels, cokernels and products by their universal properties and explains why Frobenius pullback is an equivalence of these actual R-module sheaves. This proves exactness and quasi-isomorphism detection; no theorem about a different coefficient category is borrowed.

Step 2 uses `lem-pur-ringed-site-grothendieck-abelian`, whose statement supplies all small colimits and exact filtered colimits for modules over any commutative ring sheaf on a small site. The chosen representative is small and R is such a ring sheaf. This gives the integer-indexed coproduct. I wrote the free object's structure by reindexing its translates; step 3 writes the inverse Hom correspondence on positive and negative summands. The negative recursion is valid specifically because the action is an isomorphism and T is fully faithful. Restriction to degree zero and extension are inverse, natural operations. These are explicit universal-property calculations rather than an unproved induction theorem.

Step 4 uses the same Grothendieck statement to prove exactness of the coproduct functor: it is the filtered colimit of finite direct sums of short exact sequences. The cited `lem-weil-pbc-right-adjoint-preserves-kinjective` states exactly that an additive right adjoint to an exact additive left adjoint preserves K-injectives. Steps 1-3 supply these two functors and their abelian domains, so its conclusion applies to the arbitrary I in this item. This checks the hypothesis missing in a naive invocation of 0A95.

Step 5 uses `lem-pur-rhom-well-defined` with its actual map f ↦ s f t, taking s to be the identity of UI and t=Ualpha. Its statement permits this arbitrary ring sheaf, arbitrary first complexes, and arbitrary quasi-isomorphism Ualpha. Step 4 supplies K-injectivity of both identical targets UI; step 1 supplies Ualpha's quasi-isomorphism. I checked directly that forgetting the product Hom complex gives the ordinary complex and that precomposition respects the conjugation action and the signed differential. Exact conservative forgetting then reflects the resulting quasi-isomorphism. `def-weil-abstract-derived-category` supplies localization at quasi-isomorphisms, so Q of this actual equivariant chain map is invertible.

Step 6 uses only the termwise K-injective computation in the statement of `def-sfb-right-derived-functor`, which I opened. Its arbitrary-complex K-injective-resolution framework is the framework specified in the item. Projection to the p=0 factor and insertion of zero elsewhere are mutually inverse chain maps, since the source differential is zero. They respect Weil structures and every restriction map. This computes the fixed-source derived functor without supposing H_A itself exact.

Step 7 uses `lem-weil-pbc-kinjective-hom-derived`, whose statement gives the Hom bijection in the homotopy and derived categories of any abelian category, and says quasi-isomorphisms between K-injectives are homotopy equivalences. Thus it applies in the native category A, including for unbounded chosen representatives. I checked the source and target homotopy formulas explicitly: (-1)^n f h and h' f have the correct signs. The displayed lifts of alpha_B a and of identity comparisons make the naturality and choice squares commute up to equivariant homotopy, and hence after Q. This proves both variables' naturality, not just equality of cohomology sheaves.

I checked B1-B10: no new nodes, definitions or hidden proof-bearing statements; no replacement of the item by its own conclusion; no extra hypotheses; exact verbatim citation excerpts; unchanged statement; honest search logs. For C1-C8 I opened every cited statement and checked the input hypotheses described above; generic off-unit tools are declared in `split_report.tool_uses`. For D1-D5 the main work remains in the explicit construction, invariant precomposition map and naturality argument in the item. For E1-E7 I checked the empty scheme, A=0, N=0, identity alpha, a contractible target, and nontrivial automorphism structures: all formulas remain valid. For T=id the left adjoint becomes the usual integer-orbit free object, so no false claim that forgetting is fully faithful occurs. No product-exactness assumption appears. The product over zero Hom factors is reduced by its universal property, not by an illegitimate finiteness assumption. All seven steps are below 2000 characters; no long step hides an auxiliary lemma. Nothing remains unfinished in this split.

## Validation

The required server dry run and push are performed after this report is written; their final results are recorded below.
