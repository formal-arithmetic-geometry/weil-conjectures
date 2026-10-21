# Worker report: lem-sf-normalized-derived-comparison-composition

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-normalized-derived-comparison-composition.json`: statement item, split into six proof steps; no Mathlib match.
- `citations.json`: five step/node citations with verbatim portions of the statements actually used.
- `report.md`: this report. `searches.jsonl` was produced by the required msearch commands.

New nodes: 0. New Mathlib leaves: 0. The sandbox initially contained only dispatcher brief markers, so the item was copied from the current read-only repository. Its statement, statement dependencies, source, creation record, chapter/unit, and blueprint ancestry were retained. No repository or launcher file was written, no git command was run, and no Lean file was written or compiled.

## Attachments

None. I searched `lean/WeilConjectures/` by the precise blueprint tag and by normalized derived-comparison terminology. I also inspected the composition APIs in `CategoryTheory/DerivedCategory/RightDerivedFunctor/MapDerivedComp.lean`, `CompConjugate.lean`, `IsoAlgebraComp.lean`, and `CategoryTheory/DerivedExactCompositionComparison.lean`. The superficially relevant `rightDerivedFunctorIsoMapDerivedCategoryComp_hom_app_comp` requires preservation of K-injective complexes. The item explicitly makes no such assumption and concerns three supplied comparisons across both the source and target exact functors. None of those declarations states this item under its hypotheses.

## WANTED

None. All source material used is available locally. The inherited instruction to read `coord/dag-sync.md` points to a file absent from this current shared repository; the explicit live-repository and direct-delivery instructions in the brief govern this work.

## Problems and changes

The imported item was a complete, well-typed statement with an empty proof. I found no false assertion and made no statement correction. It is important not to replace exactness by preservation of K-injectives: the proof instead chooses a K-injective resolution in each relevant category.

The complete argument is in the item, rather than delegated to a new restatement. The common-resolution sibling was already split in the current DAG. It supplies only the evaluation of the first comparison; the normalization of the other two comparisons, multiplication of inverse arrows, and the passage to arbitrary derived objects are written out here. All proof steps are below 2000 characters. The proof origin is correctly marked agent-written: Stacks 070Y supplies the underlying K-injective computation, not this exact three-comparison statement.

## Unfinished work

None for the assigned stage-1 split. No stage-2 or stage-3 work was attempted. Independent maintainer review remains the normal delivery process.

## Not duplicates

No new nodes were created. Whole-blueprint searches for `normalized derived comparison`, `K-injective-normalized`, and `comparison composition` returned no matching blueprint node. DAG searches for the phrase and for tag 070Y located the existing common-resolution and K-injective-map-computation siblings, which are reused. `lem-sf-normalized-derived-comparison-common-resolution` is strictly the two-resolution evaluation formula for one supplied comparison; it is not a theorem composing three comparisons. Scheme-specific bounded-below direct-image coherence nodes, such as `lem-cbc-etale-derived-direct-image-coherence`, also do not restate this unbounded six-category result. The nearest ancestor remains `def-weil-integral-rational-qbar-compact-support`, confirmed by `tools/blueprint_refs.py ancestor`.

## Mathlib search review

I retained all inherited search records. I ran msearch for the item using LeanFinder, Loogle, LeanSearch, and grep, followed by a second semantic phrasing and a second grep. The appended records use exactly the tool and query strings in the command-generated `searches.jsonl`, with the actual hits. All six NG requests succeeded. The earlier inherited Loogle query containing `CategoryTheory.NatIso` had an unknown-identifier error; that historical result is preserved, and the NG Loogle query succeeded.

I read `Mathlib/CategoryTheory/Functor/Derived/RightDerived.lean:100-139`, notably `rightDerivedNatTrans_comp` at line 125: it is vertical composition of transformations with a fixed localization and target. I read `Mathlib/CategoryTheory/Localization/DerivabilityStructure/PointwiseRightDerived.lean:40-129`, notably `rightDerivedFunctorComparison` at line 64 and its factorization formulas at lines 71 and 80: these construct one canonical localizer comparison with fixed target. I also read the ordinary higher-derived transformation composition in `Mathlib/CategoryTheory/Abelian/RightDerived.lean:225-245`. None states horizontal composition of three arbitrary supplied K-injective-normalized comparisons through two source and two target exact functors; identifying the supplied maps and pasting them is exactly the calculation this split provides. Thus the item is not a one-line Mathlib specialization.

## Review by NG

I read the whole item, the chapter `sec-smooth-purity`, and the unit `sk-def-sf-operations`. This generic lemma implements coherence of finite-level restriction-of-scalars transitions in the ancestor's inverse-limit formula. I read that formula in the current `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-int-brown/def-weil-integral-rational-qbar-compact-support.md`. This item is below that definition, not its unit's key node, so neither unit realizations nor the chapter route are changed. I checked tag 070Y against `literature/stacks-project/tags/tags` and read `derived.tex`, lemma `lemma-K-injective-defined`, lines 9747 onward, including its proof. That lemma says that a K-injective computes the total right derived functor. The new pasting argument is explicitly distinguished from a quotation of that source. There are no new nodes requiring additional sources, and no SGA source is used.

For step 1 I opened the full statements of `lem-weil-pbc-exact-functor-derived-factorization`, `lem-sf-kinjective-derived-map-computation`, and `def-sfb-right-derived-functor`. The first explicitly says termwise exact functors carry quasi-isomorphisms to quasi-isomorphisms. Applying it to the exact r_01 makes w = v r_01(u) a resolution with K-injective target I; neither exactness of F_0 nor preservation of K-injectives is used. The computation statement explicitly gives c_a = eta_I^{-1} RF(Qa) as an isomorphism. The derived-functor statement explicitly says eta_H is invertible for K-injective H, supplying invertibility of T after applying s_02. I changed the draft to cite this last assertion directly, rather than leave it implicit in the c_a formula. Every required resolution exists by the item's own stated hypothesis.

For step 2 I read the entire statement of `lem-sf-normalized-derived-comparison-common-resolution`, not its proof. Substituting N = r_12 H, F = F_0, G = F_1, r = r_01, s = s_01 gives exactly A beta_01 B^{-1} = X^{-1}. Its hypotheses require K-injective resolutions in A_0 and A_1, exactness of r_01 and s_01, equality F_0 r_01 = s_01 F_1, and the given normalization for beta_01; each is present verbatim in the item. Its statement expressly permits the input N and the intermediate rJ to be non-K-injective. The equation quoted in citations.json is copied verbatim from that statement.

Step 3 uses only the item's two normalization hypotheses. At H with resolution u the beta_12 equation, after s_01, has target T^{-1}; F_0 r_01 = s_01 F_1 identifies its right side with Y^{-1}. At H with resolution w the beta_02 equation has right side P_0(F_0w)^{-1}. Thus neither equation requires an unstated comparison-identification theorem. The canonical exact-functor localization identifications are expressly stipulated in the item. I checked types: Y goes from P_0 F_0 r_02 H to P_0 F_0 r_01 J, while X goes from P_0 F_0 r_01 J to P_0 F_0 I. Both are invertible by the normalization hypotheses at the K-injective complexes H and J respectively.

Step 4 is the displayed associativity and inverse calculation. The product has the order Y^{-1} X^{-1}, which is the inverse of X Y = P_0(F_0w). Inserting A^{-1}A between the comparison components is typed correctly, and cancelling T^{-1} and B^{-1} proves equality on Q_2 H. I deliberately wrote this multiplication rather than calling it compatibility or transport. It is elementary once steps 2 and 3 supply the arrows.

For step 5 I opened `def-weil-abstract-derived-category`: its statement defines D as localization of all cochain complexes at quasi-isomorphisms, equivalently of their homotopy category. A representing complex N and the assumed resolution N -> H therefore give q: L -> Q_2 H. The step expands naturality of beta_12 and beta_01 separately and composes the two equations; the equalities r_02 = r_01 r_12 and s_02 = s_01 s_12 are already hypotheses. There is no new general descent lemma hidden here. Step 6 is cancellation by the image under D_2 of an isomorphism and uses no further non-elementary fact.

I tested identity r_ij and s_ij with resolutions u = v = identity on a K-injective H: A and B become inverse derived units and all three normalized components become the identity after conjugation. I tested all F_i zero and the zero abelian category: every comparison and every displayed identity reduces to the unique arrow. I also checked an acyclic input N resolved by N -> 0 and the case r_12 H is not K-injective: the proof only uses the chosen u, so it imposes neither monicity of resolution maps nor preservation of K-injectives. With identity functors and nontrivial resolution maps, unit naturality gives the same equations, so the argument does not depend on selecting identity resolutions. No counterexample or missing hypothesis emerged.

Against delivery-errors B1-B10, no new unsplit node, undefined object, missing source tag, false leaf, unrun search, or unsupported attachment was introduced. Against C1-C8, every non-elementary input has a node whose statement I read; all five citation pairs have exact quotes, the common-resolution node does not depend on this item, and there is no off-unit non-leaf tool use. The exact-factorization node is already a Mathlib leaf and the two comparison nodes lie in this unit. Against D1-D5, the argument is carried by the six steps with no new node and no omitted standard subclaim. Against E1-E7, I checked the resolution and normalization hypotheses at their actual inputs, every arrow's endpoints and inverse order, the coefficient-free generic categories, and the expanded final naturality calculation. The statement and its meaning were preserved.

The preliminary server `review_split` check passed before report generation. The first deliver.py dry run rejected the phrase "the item's hypotheses" in step 3 under B2. I replaced it with the explicit description "the given normalization at H with precisely the resolutions u and w"; the mathematical argument and all hypotheses are unchanged. The repaired dry run and final push follow this report.
