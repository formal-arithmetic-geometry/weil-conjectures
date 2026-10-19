# Stage-1 worker report: lem-pe-kflat-roos-representative-invariance

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-pe-kflat-roos-representative-invariance.json` — existing item, completed split; no new nodes and no Mathlib leaves.
- `citations.json` — 12 verbatim statement quotations for four proof steps.
- `report.md` — this report, retaining the interrupted attempt's findings and recording its repairs.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item id and Roos/K-flat terminology found no project declaration stating every clause. The nearby `AlgebraicGeometry.ProEtale.quasiIso_whiskerRight_of_kFlat` in `SixFunctors/ProEtale/Derived/TensorResolution.lean:58` concerns tensoring on a scheme's pro-etale site with a constant coefficient category. Its inspected proof does not state this arbitrary ringed-site augmented Roos result.

## WANTED

None.

## Node/source issues and interrupted-attempt repairs

The repository item remains unsplit, with an empty proof and Lean state none. The sandbox's statement agrees with it exactly, so the statement and its dependencies are unchanged. Its blueprint ancestor is `sk-def-pe-derived-completion`, whose current completeness display motivates the extracted augmented representative-invariance assertion. I read the current unit and chapter records and blueprint text; there is no alternate route in a unit proof to replace. Whole-blueprint searches for Roos and K-flat representatives found no existing blueprint statement equal to this item.

The first resumed dry run exited with a citation-check failure: the quote for `def-sfb-left-derived-functor` was shorter than the required 40 characters. No push occurred. Reading the full statements also exposed a substantive C4 problem: the previous Step 1 applied results about sheaves valued in one fixed coefficient category directly to modules over an arbitrary ring sheaf, and Step 3 assumed an equivalence of localizations not stated in its cited left-derived-functor definition. I repaired both instead of merely lengthening the quote. The precise existing `lem-pur-change-of-rings-kflat-quasi-iso` supplies scalar-extension invariance without additional monoidal hypotheses. A right-fraction roof and `lem-pc-kflat-resolution` give a common K-flat source for the supplied derived isomorphism; the final equation is proved by strict naturality and cancellation. This removes the unsupported localization construction and its five unnecessary generic prerequisites.

The previous Mathlib searches and their log are retained. The existing imported search records are preserved as inherited records; this continuation did not rerun or invent searches. The logged LeanFinder/LeanSearch/Loogle/grep results concern generic quasi-isomorphisms, tensor exactness, and additive-functor localization, not the augmented scalar-extension Roos statement. No new node was created, so no new-node searches or same-tag duplicate comparisons are needed.

One bibliographic issue in an existing node is reported for maintenance: `lem-pc-right-fraction-representation` names the nonexistent label `categories-lemma-right-localization-finite-diagram` for Tag 04VI. In the local Stacks tag table and source the correct label is `categories-lemma-morphisms-right-localization` (categories.tex:4619). Its singleton case gives exactly the cited statement. The item's step cites that correct tag and label; I did not edit the other node.

## Review by NC

I reviewed delivery-errors B–E with the item, all cited statements, and local sources open. For the scalar-extension input I read sites-cohomology.tex Tag 06YT (`lemma-derived-tor-quasi-isomorphism-other-side`) and the change-of-rings case of Tag 06YY (`lemma-derived-base-change`), including the resolution square explaining why no flatness of the target ring is needed. For the comparison source I read Tag 06YS (`lemma-K-flat-resolution`). For roofs I read derived.tex Tag 05RT (`lemma-acyclic`) and categories.tex Tag 04VI (`lemma-morphisms-right-localization`). For the Roos model I read derived.tex Tag 08TC (`definition-derived-limit`) and the statement of the existing strict Roos comparison; for the tower's abelian structure I read homology.tex Tag 02MZ (`lemma-inverse-systems-abelian`). There are no new nodes whose sources need separate review, and no SGA source is used.

Step 1 cites `lem-pur-change-of-rings-kflat-quasi-iso`, which states precisely that extension of scalars along a morphism of commutative ring sheaves preserves quasi-isomorphisms between K-flat complexes. Its additive-functor hypothesis is verified by the map formula on elementary tensors. The module-category definition supplies sectionwise kernels and sheafified cokernels, so forgetting the extra scalar action preserves the underlying cohomology. The tensor and inverse-system definitions supply the actual strict transition and unit formulas. I checked the coordinate equalities on tensors: the transition squares commute, the units lie in the kernel of 1-s, and the two augmentation composites are equal. No flatness or surjectivity of any algebra map is added.

Step 2 cites the levelwise-abelian tower lemma for kernels, cokernels, and therefore cohomology. Thus the Step 1 map is a quasi-isomorphism of actual tower complexes. The strict Roos lemma explicitly says that its construction and maps descend to a functor on the derived category of that tower category; this is stronger than merely asserting existence of a derived limit and supplies the needed functoriality. Its site-size and exact-countable-product assumptions are exactly those of the item. I checked the cone signs against the derived-category definition: (x,y) maps to (-y,x) in Cone(1-s)[-1], with image differential (dy-(1-s)x,dx). This signed interchange commutes with the comparison maps. The same definition states cohomology factors through Q, so invertibility of Q(L(a)) really implies the stated quasi-isomorphism.

Step 3 cites `lem-pc-quasi-isomorphisms-multiplicative-system` to obtain right fractions in the homotopy category, and `lem-pc-right-fraction-representation` for the explicit roof representing e. It cites `lem-pc-kflat-resolution` for a resolution W to the roof's middle complex with BOTH K-flatness and flat terms. These are exactly what is needed to apply Steps 1–2 to its composites into P and P'. Since e and Q(t) are invertible, Q(f) is invertible; cohomology detects that f is a quasi-isomorphism. Choosing chain representatives of homotopy-category maps does not claim a direct comparison P to P' or a functorial choice of roof. The assertion only requires existence of v, so no roof-independence theorem is silently used.

Step 4 is elementary cancellation of the two strict naturality equations, giving the exact equation required by the item for v=Q(L(b))Q(L(u)) inverse. The final quasi-isomorphism criterion uses both directions: Q inverts quasi-isomorphisms and every cohomology functor factors through Q. These clauses are explicitly in the cited derived-category definition, rather than inferred from localization alone.

I checked the zero complex, the zero coefficient tower, and the constant identity coefficient tower. With zero coefficients eta is the zero map to zero, so its quasi-isomorphism condition is exactly acyclicity of P, which is invariant under derived isomorphism; the proof handles this case without cancellation of eta. All constructions still make sense for non-surjective and non-flat coefficient maps. Every step is shorter than 2000 characters and carries its argument; none hides a new comparison lemma. The generic off-unit facts are declared in `split_report.tool_uses`. Every entry of citations.json is now the full current statement of the cited node, checked against the exact use above. Definitions and existing lemmas are reused, so the delivery introduces no elementary nodes, duplicates, or restatements of the item's clauses.

## What could not be finished

Nothing mathematical remains for this one-level split. Only stage 1 was performed; no Lean file was written and no compiler, Lake, or build was run.
