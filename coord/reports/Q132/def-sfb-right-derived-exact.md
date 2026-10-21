# Worker report: def-sfb-right-derived-exact

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-right-derived-exact.json`: item, split into four proof steps. Its assertion is classified as `statement`; the original `blueprint_kind: definition` and every imported and Lean field are retained. The mathematical statement is unchanged. Added the existing exact-functor definition to statement dependencies.
- `citations.json`: one entry per step/cited-node pair, with literal substrings of the actual statements.
- `searches.jsonl`: five actual wrapper searches and their results, preserved verbatim.
- `report.md`: this report. The sandbox also contains the item-specific JSON-writing helper; it is not a delivery node.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves reused: exact-functor derived factorization and localization universal property (plus the exact-functor definition).

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint tag, the exact comparison names, and the right-derived/exact-functor notion. The upstream `CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory` and its `_hom_fac` lemma in `WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/MapDerivedCategory.lean:97,103` concern `F.rightDerivedFunctor` under `HasKInjectiveResolutions C`. That class imposes monomorphic resolution maps. The recorded dependency instead uses an arbitrary quasi-isomorphism resolution hypothesis and the chosen `rightDerivedFunctorOfQuasiIsoResolutions`. These are different interfaces and different chosen objects. The existing project-specific comparison in `lean/Sheaf/CategoryTheory/RightDerivedFunctorOfQuasiIsoResolutionsExact.lean` contains a `sorry` in its unit-compatibility theorem. Neither is an exact completed attachment under the brief. I read the entire comparison module and relevant upstream definitions; no compiler or axiom probe was run.

## WANTED

None. All sources needed for this split are present.

## Problems found and corrected

The imported proof compressed three claims into one paragraph: preservation of quasi-isomorphisms, universality of the localization lift, and uniqueness. Only the derived-functor definition was cited, which did not itself supply the first two facts. I reused the existing exact-functor factorization and localization universal-property statements and wrote the bijection and inverse equations explicitly. The imported node was classified as a definition although its text asserts existence of an isomorphism. I classified it as a statement so its proof is audited; no mathematical hypothesis or conclusion changed and no STATEMENT-DISPUTED correction is needed.

The main-20261015 source item contains a statement only, without a `## Proof` section. Its retained imported proof, the unit's exact-functors bullet/step 3, and Stacks Tag 015F give the same route. Tag 015F explicitly omits details; this delivery supplies them as an agent-written universal-property argument rather than attributing those equations to a written Stacks proof. No SGA source was used. No chapter or unit record is edited.

## Unfinished work

No stage-1 mathematical work remains in this item. Later formal proof work remains outside this brief. No Lean files are written and no build is run.

## Searches and reuse

Before choosing dependencies I searched all DAG JSON records for the right-derived, exact-functor, localization, and cohomology notions, and by the names `mapDerivedCategory`, `rightDerivedUnique`, `isRightDerivedFunctor_of_inverts`, and Tag 015F. I ran `tools/blueprint_refs.py search 'right derived functor of an exact'`, `search 'exact functor'`, and `ancestor def-sfb-right-derived-exact`; I read the candidate statements. The other exact-functor derived node also includes left derivation and bounded-below restrictions. It is not a new node and is not needed: the short universal-property proof here works directly on the homotopy-category localization specified by the dependency. The left-derived exact item has different resolution hypotheses and a different conclusion. No other blueprint node states this same chosen-right-derived comparison, so `same_as` is empty.

The five Mathlib searches recorded in the item are exactly the commands in `searches.jsonl`: LeanFinder with the exact-functor wording, Loogle with `IsRightDerivedFunctor` and `mapDerivedCategory`, grep for the comparison/uniqueness/factorization names, LeanSearch with the canonical-comparison wording, and a second LeanFinder phrasing using a localization and any chosen universal pair. All services answered. I read all hits. The second phrasing found `isRightDerivedFunctor_of_inverts` and `rightDerivedUnique`, whose full signatures I read in Mathlib. I also read `ExactFunctor.lean:29-78`, `RightDerived.lean:90-141`, `PointwiseRightDerived.lean:150-200`, and `Localization/Predicate.lean:268-360`. They give the ingredients. Combining the exact termwise factorization with its derived universal property and identifying the recorded chosen pair is the argument of this item, rather than one existing Mathlib declaration specialized to it.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish. Every auxiliary fact is supplied by an existing node or written as a short consequence of its actual statement.

## Review by Q132

I read the complete chapter and unit records, the main-20261015 item, the complete current `def-sfb-right-derived-functor` record, and Stacks `derived.tex`, Tag 015F (`lemma-right-derived-exact-functor`), especially clauses (3)-(4) and the sentence asserting preservation of quasi-isomorphisms. Tag 015F applies to exact functors of abelian categories without boundedness or injective-target assumptions. The unit route is unchanged: an exact functor needs no derived replacement. I read every cited node's statement, not just its title or proof. There are no new-node sources to review.

Step 1 uses the recorded right-derived definition for `F_K`, both homotopy localizations, and the chosen unit. The exact-functor factorization statement expressly asserts preservation of quasi-isomorphisms for additive functors preserving finite limits and finite colimits; these are precisely the additional exactness hypotheses here. The abstract-derived definition expressly allows localization of the homotopy category, and defines quasi-isomorphisms by all cohomology degrees. Representing a homotopy morphism by a chain map and applying those two statements proves that T inverts the specified class. No unproved cohomology-commutation lemma is hidden in this step.

Step 2 applies clause (1) of the localization universal-property node to that same T, with source `K(C)`, localization `D(C)`, and target `D(D)`. The abstract-derived statement specifically says this is a localization of the homotopy category. The universal-property statement allows arbitrary categories; there is no small indexing-category hypothesis to verify. Its conclusion gives both the functor and the factorization isomorphism in the orientation used here. On complexes and chain maps that factorization is literally application of F termwise followed by localization. Its clause (2) supplies the uniqueness for other choices. No identification with an unrelated chosen derived functor is presumed.

Step 3 uses precisely clause (2), existence and uniqueness of a lifted natural transformation. Both functors being compared factor through Q, so both invert the class required by that clause. Composing beta with phi gives exactly a transformation between those two composites; the comparison isomorphisms for clause (2) can be identities. The equation gamma Q = beta phi is equivalent to (gamma Q) epsilon = beta because epsilon = phi inverse. This proves both surjectivity and injectivity of the exact natural-transformation map displayed in `def-sfb-right-derived-functor`. It is a generic non-elementary localization result and is marked non-elementary and cited, rather than asserted from a definition alone.

Step 4 uses the actual universal-pair clause in `def-sfb-right-derived-functor` and the bijection established in step 3. I checked the direction of each transformation: a:RF -> D(F) sends eta to epsilon, b:D(F) -> RF sends epsilon to eta. The two composites therefore send each unit to itself, so injectivity identifies each composite with its identity. This is a short elementary calculation from the stated bijections, not a new lemma or restatement-node. It proves the whole canonical-isomorphism assertion, including compatibility with the specified units, and handles alternative choices through the uniqueness already proved.

I checked delivery-errors B1-B10: no new unsplit proof sketches, malformed new statements, duplicated notions, fabricated searches, or unverified leaf claims occur; blueprint and source metadata are retained and completed. For C1-C8 every non-elementary fact is covered by the cited statements just described; the two off-unit generic tools are already Mathlib leaves, so no worker-authorized tool-use exemption is needed. The definition dependency is in the same unit. For D1-D5 the proof carries the argument and fills Tag 015F's omitted details; no new node restates a clause, and no argument uses its own conclusion. For E1-E7 I checked all hypotheses and all map orientations explicitly. The statement itself is true, with no source correction required.

Small cases: the zero functor, zero category, zero complex, and identity functor satisfy the same localization bijections and comparison equations. An acyclic complex maps to zero in both derived categories, and any quasi-isomorphism maps to an isomorphism; there is no nonzero restriction. Arbitrarily unbounded complexes are included. Only the source resolution hypothesis inherited from the definition is present, and it is used to supply RF, not to construct D(F); the proof never strengthens it to monomorphic resolutions or assumes enough injectives in the target. No countability, exact products, field characteristic, coefficient ring, finite-index category, or bounded-below condition enters. All categories and functor categories are understood in the chosen localization universes from the abstract-derived node. Every step is under 1000 characters and carries no hidden long comparison lemma.

## Validation

The required `deliver.py --no-push` and final delivery are run after this review. Results will be appended after each command exits.

The dry run exited 0 and printed `OK (not pushed) deliver/Q132/def-sfb-right-derived-exact at 5f70821dcfa: preflight passed`. This is the required server preflight, including the DAG and split checks. All four steps have explicit sources, citations, and elementary flags; their lengths are 738, 832, 898, and 733 characters. No local check script, compiler, Lake, git command, or repository write was performed. The final authorized push follows this successful dry-run receipt.
