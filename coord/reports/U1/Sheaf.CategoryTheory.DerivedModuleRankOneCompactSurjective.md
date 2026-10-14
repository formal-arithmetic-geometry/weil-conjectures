## What changed

Proved `CategoryTheory.derivedModule_rankOne_comparison_surjective` in
`Sheaf.CategoryTheory.DerivedModuleRankOneCompactSurjective`, with its signature unchanged.
Added three proved private helpers: `rankOne_kProjective`, `rankOne_map_surjective`, and
`rankOne_chain_finite_sum`. The proof uses K-projective localization to lift a derived map,
then computes the finite support of a chain map by evaluating on the lifted unit. Coproduct
projections give the coordinate chain maps. Finally `derivedModuleDirectSums` and the
canonical representative isomorphisms transport the finite sum to the required coproduct.

Added proof-only imports of `Mathlib.Algebra.Homology.DerivedCategory.KProjective`,
`Mathlib.Algebra.Category.ModuleCat.Projective`, and
`Mathlib.Algebra.Category.ModuleCat.Products`. Existing public imports and declaration
visibility are unchanged. Updated the existing node's proof and proof origin to record the
implemented chain-map calculation; its dependency on `lem-pc-derived-module-direct-sums`
is retained. No existing statement, definition, or other module was changed.

Validation: the complete file compiles cleanly through `lcompile.py`. The source is
Stacks Project Tag 0F5X, first paragraph, which asserts compactness of the regular module;
the explicit calculation here supplies that assertion's finite-support argument. The
argument requires no commutativity or nonzero-ring hypothesis, and the support construction
works for the empty index type. No arbitrary witness of an unproved existence statement is
used to define data: the representatives and colimit isomorphisms use proved universal
properties. Searches were run through `msearch.py` using LeanFinder, Loogle, and grep;
Loogle located `CochainComplex.IsKProjective.Qh_map_bijective`, while no complete compactness
result was found. Local searches also checked both library roots and Mathlib.

## Proved and sorry left

Closed one original hole:
`CategoryTheory.derivedModule_rankOne_comparison_surjective`
(node `new-stage3-derived-module-rank-one-compact-surjective`).
No `sorry` remains in this module. No holes were added, and no statements were split off.
All three private helpers are fully proved. This is a proof, not a decomposition.
The existing proof dependency `CategoryTheory.derivedModuleDirectSums` is retained.

## No longer needed

No original import, node, or module is pruned: the sole planned proof dependency,
`Sheaf.CategoryTheory.DerivedModuleDirectSums`, is used. A trial explicit import of
`Mathlib.Algebra.Homology.HomologicalComplexAbelian` was redundant and is not retained.
The proof does not require a separate additive Hom/H-zero identification, cycle lifting,
or a new cohomology-commutes-with-direct-sums statement; these were explanatory parts of
the old plan, not separate DAG dependencies.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. Tag 0F5X asserts the compactness fact without expanding this
calculation. The earlier plan can be implemented more directly at the chain-map level:
coordinate projections preserve the chain-map condition automatically, so one need not
construct individual cycle representatives or separately formalize Hom/H-zero naturality.
The unit has no realized statement or proof-step nodes in `dag/units/sk-prop-sf-cbc.json`;
no required unit step is bypassed.

## Second reading by U1

1. **Unchanged interface — PASS.** Read the entire delivered module and compared it
   with the repository using `diff -u`. Also compared the existing theorem's signature
   as literal text: it is byte for byte identical. The only Lean changes are the proof,
   three proved private helpers, three plain proof imports, and a module comment.
   No existing definition, statement, public import, or visibility changed; no change
   record is needed. The sandbox contains only this delivered Lean module and the
   existing node's update.
2. **Proof and axioms — PASS.** Independently compiled the delivered file through
   `lcompile.py`, cleanly. A scratch copy with `#print axioms` for the public theorem
   and all three private helpers compiled and printed exactly `propext`,
   `Classical.choice`, and `Quot.sound` for each. A source scan found no `sorry`,
   forbidden declaration, or implementation attribute. Read the K-projective lifting,
   degree-zero finite-support calculation, and coproduct transport line by line.
   The representatives come from the proved essential-surjectivity API; the selected
   colimit structure satisfies a universal property and is unique. No data is chosen
   from an unproved arbitrary-existence theorem.
3. **Split statements and edge cases — PASS.** There are no split-off statements,
   new public declarations, or new holes. The private helpers are fully proved and
   strictly describe parts of the argument. For an empty index type the concrete
   direct sum and its support are zero and empty, so the constructed preimage is
   the empty sum. For the zero ring the lifted unit is zero and the same linearity
   calculation applies. The identity `a = a.down • ULift.up 1` needs no commutativity.
   Independent LeanFinder, Loogle, and grep searches used coproduct factorization
   and surjective-localization wording; local searches checked both library roots
   and Mathlib. No independent complete replacement was found. The compactness
   result above this item depends on this very theorem and cannot replace it.
4. **Top-down route and pruning — PASS.** The proof directly opens the original hole,
   uses Mathlib's bounded projective-complex theorem and localization bijection,
   computes finite support on chain maps, and uses the existing
   `derivedModuleDirectSums` dependency to transport the result. Independently
   removed each added proof import in separate scratch copies: without Products the
   concrete coproduct theorem is unavailable; without Projective the projectivity
   instance fails; without KProjective its predicate and localization APIs are
   unavailable. All added imports are plain imports. The sole old proof dependency
   is used, so `## No longer needed` is complete. The associated unit record has
   empty realized statement and step lists, and no prescribed unit step is bypassed.
5. **DAG and source — PASS.** Compared the existing node with its sandbox version:
   only `proof` and `proof_origin` differ. Its three proof steps accurately describe
   the two lifting helpers, the finite-support helper, and the final transport.
   The union of step uses is exactly `proof_deps`, namely
   `lem-pc-derived-module-direct-sums`. The Lean record still states the unchanged
   theorem. There are no new nodes requiring extra fields. Checked Stacks Project
   Tag 0F5X, first proof paragraph, which asserts compactness of the regular module;
   the delivered calculation supplies the surjectivity part of that assertion.

Second reading changed only this report, adding the independent checks and verdicts.
No proof, signature, import, definition, or node repair was necessary. One original
hole is closed, zero holes are added, and zero statements are split off.
