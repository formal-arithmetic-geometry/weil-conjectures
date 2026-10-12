## What changed

Completed the proof of `AlgebraicGeometry.isLocallyConstructible_section_component`.
The proof uses the local noetherian model and generic dichotomy modules, then performs
noetherian induction and pulls constructibility back along the projection. Added DAG
records for the two intermediate declarations and updated the item proof dependencies.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.isLocallyConstructible_section_component`.
Added two holes, so this is a decomposition (one closed minus two added = -1),
not a complete proof from axioms. No `sorry` remains in the item's module. The imported
intermediate declarations `exists_section_component_noetherian_model` and
`exists_open_section_component_dichotomy` remain named `sorry` theorems in their own
modules, with nodes `lem-sbc-section-component-noetherian-model` and
`lem-sbc-section-component-generic-dichotomy`.

## No longer needed

No imports or DAG dependencies were removed. The proof needs the constructibility
criterion module, the noetherian model, and the generic dichotomy.

## Where the brief, the DAG or earlier work was wrong

The original item node had an empty proof dependency list despite its proof requiring
local noetherian descent and the generic dichotomy. The delivery records those
dependencies explicitly. The earlier sandbox's noetherian-induction proof compiles. It had no report or
DAG records; this attempt supplies both. Tags 055P, 055N, and 055M were read and
confirm the two reductions. Neither intermediate is a restatement: the model
lemma supplies an inverse-image representation without constructibility, and the
dichotomy lemma is confined to noetherian schemes and does not assert
constructibility. All resulting witnesses are used solely in a proof of a proposition;
no data definition chooses an arbitrary object from an unproved existence theorem.

Edge checks: for the identity morphism the component is the whole source and the
positive dichotomy branch applies; for a disconnected constant family the component
is the section's summand; for empty P the local theorem is vacuous. Empty Z is excluded
by `IsIrreducible`. The model construction retains the entire inverse image of an
open of T, rather than an arbitrary affine patch of P, so fibres and section components
are preserved. No blueprint unit statement or realized step is bypassed.

## New nodes

`lem-sbc-section-component-noetherian-model` records the local descent reduction.
`lem-sbc-section-component-generic-dichotomy` records the irreducible-closed-set
alternative used in the noetherian induction.

## Second reading by F3

1. I compared the delivered item module with the repository version. The theorem signature and all existing declaration statements are unchanged; only proof imports and the proof body differ. Verdict: pass.

2. I compiled all three delivered modules with the sandbox compiler. They compile without errors or warnings, and the item theorem contains no `sorry`; the two explicitly split intermediate theorems are named public `sorry` theorems with source explanations and matching DAG nodes. Verdict: pass.

3. I checked the reduction for the noetherian model, noetherian induction, generic dichotomy, and constructible preimage. The two added statements are strict intermediate reductions rather than restatements of the item and are used in the proof. Verdict: pass.

4. The proof follows the stated route through the local noetherian model and generic dichotomy. The constructibility criterion import is used, and no unused import or old proof dependency was found. Verdict: pass.

5. The DAG records match the Lean declarations and proof dependencies, and the unit route is retained; no unit statement or realized step is bypassed. Verdict: pass.

I changed no source statements or definitions. I added this second-reading record only.

Additional verification: explicit `#print axioms` probes for all three delivered
declarations report exactly `propext`, `Classical.choice`, `Quot.sound`, and
`sorryAx` (the latter from the two documented open lemmas). No forbidden declaration
or data definition occurs. Independent Lean Finder searches for noetherian approximation
with a section returned finite-presentation and affine-transition-limit results, not
the required component equality. Loogle and Mathlib/local-library searches found no
replacement for either geometric lemma. The upstream affine relative-component results
do not supply the global scheme result; the slicing route also imports this item.
I checked the geometric arguments against https://stacks.math.columbia.edu/tag/055P,
https://stacks.math.columbia.edu/tag/055N, and
https://stacks.math.columbia.edu/tag/055M. Identity morphisms, disconnected constant
families, the empty source, and the nonempty irreducible-set requirement agree with
both split statements. Neither open lemma is plausibly closable in a few minutes:
they require formal geometric descent and generic spreading results. The original
node's proof dependency list was empty, so the pruning list is complete. The unit's
`realized` lists are empty and unchanged; the delivery remains below the slicing step.
Second-reading changes: report and independent search evidence only; Lean and DAG
content retained.
