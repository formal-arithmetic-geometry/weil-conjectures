# Stage-1 delivery: lem-trf-ringed-scalar-universal-resolution-comparison

Group Q22; 2026-10-23. Direct delivery, reviewed by the author as required by the dispatch brief.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-ringed-scalar-universal-resolution-comparison.json`: statement retained verbatim; eight proof steps; status split; source, blueprint placement, searches and off-unit tool declarations supplied.
- `citations.json`: ten entries, one for every step/node citation, checked as literal substrings of the current cited statements.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified evidence. `write_split.py` is sandbox preparation only.

There are **0 new nodes and 0 new Mathlib leaves**. Every required supporting result already has a DAG node. No unit or chapter record is changed: this item is not their key statement.

## Attachments

None. The exact blueprint tag has no declaration in `lean/WeilConjectures/`. Searches of that library for K-flat counits, universal counits, `totalLeftDerived`, scalar extension and resolution comparisons find specialized finite-coefficient constructions and ordinary-module or scheme pullback comparisons. None states every clause for arbitrary ring sheaves on a small site. In particular the native finite-coefficient `Derived/ExtendScalars.lean` does not attach this general ring-sheaf theorem. Existing Sheaf declarations and the Lean metadata of the reused nodes are reference material; the dispatch attachment rule requires an exact project declaration under WeilConjectures.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## What needed repair

The imported item had no proof. Its statement is mathematically consistent and remains unchanged. It is essential to use **all** K-flat complexes as the resolving class: the existence theorem gives representatives with flat terms, but invariance must also hold for K-flat complexes without flat terms. I reused the actual invariance statement, rather than imposing the flat-terms restriction of the more general geometric pullback construction in Tag 06YY. I also separated exactness on the homotopy category from exactness on the underlying abelian categories; the latter is not asserted for a nonflat ring map.

No source error or STATEMENT-DISPUTED claim arose. The generic right-Kan convention agrees with the item's direction of natural transformations. Its uniqueness must respect the counit; an unspecified isomorphism of functors would not establish the displayed formulas.

## Unfinished work

None within this one-level stage-1 split. The reused non-leaf nodes keep their own proof obligations and statuses. No Lean was written or compiled.

## Existing nodes reused and duplicate checks

The DAG and blueprint searches for K-flat resolutions, derived change of rings, additive homotopy functors and universal resolution comparisons found the existing supporting nodes. `tools/blueprint_refs.py ancestor` confirms the ancestor `lem-trf-local-term-locality`. The current main-20261015 chapter, unit and ancestor proof were read; this item stays on the inherited auxiliary ring/sheaf branch through `lem-trf-one-point-derived-ring-identification`, old steps 9 and 12. It does not replace the contracting-correspondence argument in the unit.

- `lem-trf-additive-homotopy-triangulated` supplies general additive homotopy exactness.
- `lem-pur-homotopy-category-triangulated` supplies exactness of localization.
- `lem-pc-kflat-resolution` supplies general ringed-site K-flat resolutions, unlike the small-etale-only flat-resolution nodes.
- `lem-pur-change-of-rings-kflat-quasi-iso` supplies arbitrary K-flat scalar invariance.
- `lem-pur-left-derived-from-kflat-class` supplies the universal derived pair after its hypotheses have been checked.
- `lem-pur-derived-change-of-rings` identifies the previously named functor, but is not used as a replacement for the normalization argument.

No new node was created, so there are no new/existing same-tag pairs requiring a `Not duplicates` section. The generic homological lemmas outside this unit are declared in `split_report.tool_uses`, with the reason for each, rather than set as approved top-level tool uses.

## Mathlib search evidence

I retained the item's inherited searches and read their results. I additionally ran all four prescribed tools with the item's id and a second LeanFinder phrasing, followed by a targeted grep for the generic derived-functor interface. Every new recorded query is copied verbatim from this sandbox's `searches.jsonl`. All services answered for these calls.

The first natural-language searches return `CategoryTheory.Functor.totalLeftDerived` and `totalLeftDerivedCounit`, ordinary `ModuleCat.extendScalars`, presheaf sheafification adjunctions and unrelated universal derivations. The second phrasing finds dense-subsite counit results and bounded ordinary right-derived results. The ringed-module grep and the combined Loogle query return no hits. I read `Mathlib/CategoryTheory/Functor/Derived/LeftDerived.lean`, especially lines 45–94, 126–137 and 183–207. Its total-left-derived construction assumes `HasLeftDerivedFunctor`; it does not prove existence and computation on all K-flat ring-sheaf complexes. Thus these hits are not a one-line specialization establishing this item. The generic interface explains the universal convention, but the item is not a Mathlib leaf.

## Review by Q22

I read Stacks `derived.tex`, Tag 014X (`lemma-additive-exact-homotopy-category`), the full dual assertion of Tag 06XN (`lemma-find-existence-computes`), and the everywhere-defined discussion and equation-everywhere. I read `sites-cohomology.tex`, Tag 06YS (`lemma-K-flat-resolution`), Tag 06YT (`lemma-derived-tor-quasi-isomorphism-other-side`) and Tag 06YY (`lemma-derived-base-change`), including their proofs where used. The source gives the existence route; the expanded naturality, cancellation and counit-uniqueness calculations are explicitly marked as agent-written assembly. There are no new nodes requiring additional sources.

For step 1, I opened `def-pur-sheaf-tensor-product` and checked that it gives the actual sheafification of the sectionwise tensor, so the displayed generator calculation establishes additivity. `def-weil-sheaf-of-modules-category` states abelianness under exactly the relative-smallness hypothesis present here. `lem-trf-additive-homotopy-triangulated` requires an additive functor between abelian categories and concludes unbounded homotopy exactness. `lem-pur-homotopy-category-triangulated` explicitly states that localization is exact. These statements prove exactness of F; there is no flatness assumption hidden in this step.

For step 2, I opened `def-pc-kflat-complex`, `lem-pc-kflat-resolution`, `lem-pur-change-of-rings-kflat-quasi-iso` and `def-weil-abstract-derived-category`. The first defines a resolution as a quasi-isomorphism with K-flat source; the second works on a general ringed site and supplies such a resolution. The third expressly accepts all K-flat complexes and an additive functor agreeing on objects and maps with actual scalar extension, which is exactly E from step 1. The fourth expressly identifies D as the localization at quasi-isomorphisms. This checks both hypotheses needed next, without using only a definition in place of an invariance theorem.

For step 3, I read the full statement of `lem-pur-left-derived-from-kflat-class`. Its source and target are of the required kind; its two resolving-class assumptions are exactly step 2. Its conclusion explicitly includes universal right Kan extension, exactness and invertibility on the entire class. “Universal among pairs” here gives existence and uniqueness of a factorization for every functor H, so the required Nat bijection follows directly; no small diagram colimit is introduced and no exactness hypothesis is added to H.

For step 4, I read the statement, not the proof, of `lem-pur-derived-change-of-rings`: it calls its functor the everywhere-defined left derived functor of this same termwise change of rings. The universal pair of step 3 therefore compares to that pair. The displayed equations construct both comparison arrows and show they are inverse using injectivity in the universal property. This is a short argument from the already established property, not a new lemma or a citation to an unrecorded uniqueness theorem. It also proves that a different universal pair has invertible K-flat counits.

For step 5, I checked types: both theta factors have the stated directions, Qq is invertible because q is a quasi-isomorphism, and naturality at q gives exactly the augmentation equation after right cancellation. Fq need not be invertible, which is why no inverse of it appears. Step 6 uses naturality at b and only the two augmentation inverses, and writes the commuting-square rearrangement explicitly; neither a nor b is inverted. Step 7 calculates identity, three-resolution cocycle and augmentation equations, and shows that a supplied strict comparison over X induces this same comparison; no strict comparison between arbitrary resolutions is assumed to exist. Step 8 writes the change-of-pair equation using naturality of the unique u, then cancels u to show that the comparison is unchanged. These four steps use only equations and invertibility already established, so are elementary and need no extra nodes.

I checked the B–E return checklist against the delivered JSON and the open sources: no statement-only new node is smuggled into a proof, no non-elementary theorem is supplied only by a tag, every uses-entry has a verbatim statement quote, and the proof does not extract a stronger conclusion from any cited proof or definition. No clause is merely renamed as a new node. All eight steps are shorter than 2000 characters (largest 836), and the elementary comparison steps contain the actual equations rather than “transport” as an unexplained argument.

For edge cases I checked zero complexes and the zero coefficient ring (the formulas are identities in the zero derived category), identity resolutions (theta is the corresponding counit), coincident resolutions (comparison is the identity), and a nonflat coefficient map on the one-object site, such as Z to Z/2. The last case confirms why T need not preserve arbitrary quasi-isomorphisms and Fq need not be invertible. An arbitrary morphism a or b is allowed in the square calculation. The proof never uses a lower/upper cohomological bound, termwise flatness of an arbitrary chosen P, or flatness of the coefficient map.

## Validation

The required direct-delivery dry run and push are run after this report is written; their final results are recorded below when available.
