## What changed

Proved `CategoryTheory.injective_split_tower_extension` directly in
`Sheaf.CategoryTheory.InjectiveSplitTowerExtension`, with its existing signature unchanged.
The successor formula is `t + (b - t ≫ p) ≫ section_ p`, where `t` is an injective
extension at the new level and `b` is the previous lift after the transition in B.
Recursion carries the extension equation; `NatTrans.ofOpSequence` supplies naturality.
Added two proof-only imports: `Mathlib.CategoryTheory.Functor.OfSequence` and
`Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono`. Both public imports stay unchanged.
Corrected the docstring's inaccurate attribution to a compatible-lifting footnote.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.injective_split_tower_extension`.
Added zero holes. No `sorry` remains in any delivered module.
This is a proof, not a decomposition: net holes closed = 1.
The proposed hole `CategoryTheory.exists_component_lift_of_injective_split_tower`
and its unlanded module/node were removed rather than delivered.
A scratch-copy `#print axioms CategoryTheory.injective_split_tower_extension` reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the proposed import/module `Sheaf.CategoryTheory.InjectiveSplitTowerExtensionComponents`
and unlanded node `lem-pc-injective-split-tower-extension-components`.
Removed every old proof dependency: `lem-pc-injective-split-tower-injective`.
The proof uses no project theorem; its only external proof tools are proved Mathlib declarations.
No existing library import was removed, and no existing library module is claimed pruned.
`Sheaf.CategoryTheory.InjectiveSplitTower` still uses this extension theorem; its theorem
was not used to prove the extension theorem, avoiding the old circular proof dependency.

## Where the brief, the DAG or earlier work was wrong

The first worker's componentwise theorem was equivalent to the item: a compatible family
with the factorization equation is exactly the natural transformation requested by the item.
Its categorical assembly did not justify calling the remaining theorem strictly simpler.
It would have closed one hole and added one equivalent hole, with no net proof progress.

The old DAG proof cited `lem-pc-injective-split-tower-injective`, whose Lean proof itself
applies this extension theorem. Replaced that circular plan by the actual recursive argument.

Read https://stacks.math.columbia.edu/tag/07KW: its current proof discusses ML envelopes
and derived inverse limits; it contains no compatible-lifting footnote. The direct proof
is therefore recorded as agent-written, with the tag retained only as related context.
No theorem statement, target definition, chapter route, or unit route was changed.

## Second reading by F1

1. Compared the delivered module with the repository version by diff and checked the
   original theorem signature byte for byte. Verdict: unchanged hypotheses, universes,
   conclusion and visibility; no definitions or other public declarations added.
   No change record is needed. Only the proof, docstring and proof-only imports changed.
2. Compiled the module with `lcompile.py`, without errors or warnings. The final proof
   has no `sorry`, forbidden declaration, or hollow definition. Printed its axioms in
   a scratch copy: exactly `propext`, `Classical.choice`, `Quot.sound`.
   Local recursive data use only proved Mathlib injectivity and split-epi results.
3. Rejected the proposed componentwise split as an equivalent restatement and removed
   its module/node. Searched Mathlib using LeanFinder (inverse systems with split
   surjective transitions), Loogle (`CategoryTheory.Injective.factorThru`), and grep
   (`NatTrans.ofOpSequence|Injective.factors|IsSplitEpi.id`); also searched both library
   roots and upstream sources. Used the existing Mathlib tools. No new statement remains.
   The correction formula also works when a component is zero, when p is an identity,
   and when f is an identity; its two identities are proved without extra assumptions.
4. Read from the target down. The direct successor correction avoids kernels and new
   project lemmas. Independently removing each added proof-only import in a scratch
   copy fails: EpiMono is needed for `Mono (f.app _)`, OfSequence for `ofOpSequence`.
   The report lists the entire old proof_deps edge removed. Read
   `dag/units/sk-thm-picard-duality.json`; its realized fields are empty and this item
   is an auxiliary tool below the unit. The unit and chapter route are unchanged.
5. Read the old and proposed node files. Replaced the existing node's proof with the
   base case, successor correction, and recursive natural-transformation assembly.
   Set proof_deps to the empty union of the steps' uses, and proof_origin to agent.
   Kept its statement, source, stmt_deps, chapter and unit unchanged. No new nodes remain.

Second reading changed: replaced the equivalent split with a complete recursive proof,
removed its new module/node, corrected the source attribution, and repaired the DAG route.
