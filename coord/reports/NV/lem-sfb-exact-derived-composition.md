# Worker report: lem-sfb-exact-derived-composition

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-exact-derived-composition.json: statement; split using existing Mathlib leaves. No new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement quotation for each dependency of each proof step.
- report.md: this report. searches.jsonl is the unmodified search-command log.

## Attachments

No full attachment claimed. I read CategoryTheory.Functor.mapDerivedCategoryCompIso at lean/WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:175 and mapDerivedCategoryCompIso_fac at :202 (through :216). Both bodies have no sorry and give the comparison and the normalization equation. They do not state uniqueness among all natural isomorphisms satisfying that equation, an explicit clause of this item. Searches for the blueprint tag and for a uniqueness/extensionality declaration in WeilConjectures found no project declaration giving that remaining clause. The imported lean_candidates are retained as partial candidates, not promoted to a full attachment.

## WANTED

None. All sources used are available locally.

## Problems found and changes

The item had an empty proof. Its statement is correct and has been retained verbatim, as have its source, provenance, blueprint ancestor, and existing search records. The new proof has four short steps. The original source correctly distinguishes Stacks 04VG's functor factorization from the stronger natural-transformation universal property; I retained that distinction. This split is marked agent-written because the explicit two-dimensional lifting argument is supplied using Mathlib, rather than falsely attributed to Stacks 04VG alone.

I read the current blueprint's def-sfb-derived-extend-comp-iso.md and .proof.md, in unit sk-thm-sfb-qlbar-two-colimit, together with that unit and chapter records. This item realizes the sentence on the derived functor of a composite of exact functors. The unit's scalar-extension and finite-field-descent route is retained. This item is not the unit's key node; no unit record is changed.

The inherited Mathlib search records were preserved. Five new searches were run with the mandated msearch.py, including LeanSearch, Loogle, grep and two LeanFinder phrasings; all services answered. The online Loogle index lists mapDerivedCategoryCompIso in Mathlib, but the pinned Mathlib source lacks it. I read pinned ExactFunctor.lean:1-110 and Predicate.lean:278-362. The former supplies exact factorizations, and the latter supplies lifting and extensionality. These ingredients already have DAG nodes, so the item remains a split rather than a direct Mathlib leaf.

## Not duplicates

No new nodes. The whole-blueprint searches for localization and exact functor, the ancestor lookup, and DAG searches for 04VG, liftNatIso, fullyFaithfulWhiskeringLeft and composite-derived-functor wording led to the existing localization and exact-factorization leaves, which are reused. The item has no other blueprint node stating its full normalized composition/uniqueness assertion; same_as remains empty.

## Review by NV

I read coord/delivery-errors.md B through E against the actual node statements and sources. For the item I read the blueprint sentence quoted above, Stacks categories.tex, lemma-properties-left-localization (Tag 04VG, around lines 4406-4435), and Mathlib Predicate.lean:278-362. Stacks gives ordinary functor factorization; Mathlib's fully faithful precomposition, liftNatTrans_app, liftNatIso and natTrans_ext give exactly the additional natural-transformation claims. No SGA source is used. There are no new node statements requiring a separate source audit.

Step 1 uses the statement of lem-weil-pbc-exact-functor-derived-factorization, not its proof: its hypotheses explicitly mean additive and preserving finite limits and colimits, exactly those of F and G here. A finite cone preserved first by F then G is preserved by GF, so the same leaf applies to GF. Its statement explicitly says the termwise functor preserves quasi-isomorphisms and supplies the required natural isomorphisms. Thus H in step 3 really inverts the source quasi-isomorphisms.

Step 2 uses the same leaf solely for those natural factorizations. I checked the intermediate object Q_B C(F)K and both ends of beta_K. Whiskering and composing natural isomorphisms is elementary; the objects, differentials and maps of the two termwise composites agree degree by degree. This step is marked elementary relative to its cited factorizations, rather than made into a new node. No tensor or derived-functor composition theorem is being silently assumed.

Step 3 uses def-weil-abstract-derived-category for precisely its assertion that Q_A localizes cochain complexes at quasi-isomorphisms. I opened lem-weil-pbc-localization-universal-property and verified that clause (2) gives both the component formula and that an isomorphism lifts to an isomorphism. In its notation both source functors are H, their lifts are D(GF) and T, and their factorization maps are a_GF and beta. Its formula therefore reads beta_K inverse followed by a_GF,K in ordinary composition notation, with no reversal of the requested compositor. Multiplication by beta_K is the required equation. The localization universe is the one already assumed for the unbounded derived categories; no small indexing category or resolution is introduced.

Step 4 uses the actual clause (3) of the same node, which determines transformations from their components on localized complexes. I checked cancellation of beta_K and equality of inverse transformations. Thus uniqueness is proved for all natural isomorphisms satisfying the equation, not only for a particular chosen construction. Every cited node's statement has a verbatim quote in citations.json, and proof_deps is exactly the union of the uses lists. All three dependencies are existing Mathlib leaves, so no off-unit tool declaration is required and no dependency can create a cycle through this item.

For edge cases I checked F or G the zero functor (all relevant complexes and comparison maps become zero-object isomorphisms), an identity functor (the equation still uniquely determines the comparison for the chosen factorizations), and genuinely unbounded complexes (the proof never truncates or takes a resolution). Arbitrary choices of the factorization isomorphisms are harmless: beta and a_GF fix the component formula and hence uniqueness. No hypothesis was added, no conclusion removed, and no statement dispute arose. The four step lengths are below 500 characters each, so none hides a long inline sublemma. B's self-contained-statement and TeX checks, C's statement-use checks, D's prohibition on moving the conclusion to a new node, and E's typing and hypothesis checks all pass on this reading.

## Unfinished work

None in the authorized stage-1 split. No Lean was written and no compiler, Lake or build command was run.
