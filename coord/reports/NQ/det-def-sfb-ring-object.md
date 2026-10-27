# Worker report: det-def-sfb-ring-object

## Files written

- `dag/nodes/sec-proetale-coefficients/det-def-sfb-ring-object.json` — the imported definition, split into one assembly step using four existing detail nodes; no Mathlib leaf.
- `citations.json` — four verbatim statement quotations for step 1.
- `searches.jsonl` — eight Mathlib searches run for this item, with the original tool records retained.
- `report.md` — this report.

Zero new nodes and zero new Mathlib leaves. Nothing was written to the shared repository or launcher, no git command was run there, no Lean was written, no compiler/Lake/build tool was invoked, and no agents were started.

## Attachments

None. The current read clone contains component declarations in `WeilConjectures/CategoryTheory/RingObjects/RingPresheaf.lean` (`Functor.toMonAb`, `Sheaf.monObj_presheafToSheaf_obj`, `Sheaf.monObj_sheafCompose_obj`, and related instances), but no single project declaration states all three clauses of this item under the item’s hypotheses. The prior attachment attempt and its rejection were read; I do not repeat that attachment claim.

## WANTED

None. The current blueprint and the existing DAG detail nodes provide the route and sources.

## What was wrong or incomplete

The imported item had only a bare assembly sentence, no step source, no citations file, empty Mathlib-search metadata, and `blueprint.same_as: null`. I supplied the current latest blueprint source and recorded the required searches. The parallel reviewed umbrella `sk-def-sfb-ring-object` has the same ring-object clauses plus an explicit sheaf-tensor formula and size convention; it is recorded as `blueprint.same_as`, while this item keeps its four detail-node decomposition. No statement correction was needed. The previous rejected attachment would have covered only a partial component, so the item remains a split rather than an attachment.

## Not duplicates

`det-def-sfb-ring-object` vs `sk-def-sfb-ring-object`: the umbrella node states the same three ring-object clauses together with an explicit objectwise/sheafified tensor formula and an essentially-small size convention; this item instead points to `lem-weil-pbc-sheaf-tensor-closed` and decomposes the clauses through the four `det-def-sfb-ring-object-*` detail nodes. The parallel statement is recorded in `blueprint.same_as`; no replacement node was created.

## Review by NQ

I read the current item, its latest blueprint file, the `sec-proetale-coefficients` chapter and `sk-prop-pe-condensed-point` unit, and the complete statements of all four cited detail nodes. I also read the current `RingPresheaf.lean` source to check the project declarations used by the attachment search. The item’s tensor convention is supplied by `lem-weil-pbc-sheaf-tensor-closed`, whose statement gives the essentially-small site, sheafified objectwise tensor, unit, and strong monoidality of sheafification; the item’s reference to that node is therefore typed correctly.

Step 1 uses `det-def-sfb-ring-object-monoid` for the definition of a monoid object, morphism compatibility, the category and faithful forgetful functor, and braided commutativity. Its statement contains exactly the associativity and two unitor equations used by the item. It uses `det-def-sfb-ring-object-rings` for the unit map `n ↦ n·1`, multiplication `a ⊗ b ↦ ab`, ring-homomorphism compatibility, and commutativity for ordinary rings. It uses `det-def-sfb-ring-object-presheaf` for objectwise presheaf multiplication and unit, naturality of presheaf ring maps, commutativity, and the sheafified structure `a(P ⊗p P) → aP` with its unit and morphism preservation. It uses `det-def-sfb-ring-object-sheaf` for the underlying abelian sheaf, the unique transported structure through the sheafification counit, the unique extensions of multiplication and the integer unit, commutativity, and morphisms of sheaves of rings. The four full statements are copied verbatim in `citations.json`, so every fact taken by the assembly step is present in its cited statement rather than only in a proof or docstring.

I checked the hypotheses and edge cases explicitly: arbitrary unital rings include the zero ring; noncommutative rings use only the monoid-object clauses and acquire commutativity only under the stated commutativity assumption; presheaf restrictions preserve products and units objectwise; a sheaf of rings is already a sheaf in the underlying abelian category; and empty or terminal sites do not add hypotheses. The existing umbrella `sk-def-sfb-ring-object` was read as a parallel statement, not substituted for any detail node, and the distinction is recorded above. All proof dependencies equal the union of the step’s uses. The assembly step is sourced to the latest blueprint’s `## Proof`, contains no hidden lemma, and is well below the long-step threshold.

## Unfinished work

None for this stage-1 split. The required remote dry run and delivery remain the final validation steps.
