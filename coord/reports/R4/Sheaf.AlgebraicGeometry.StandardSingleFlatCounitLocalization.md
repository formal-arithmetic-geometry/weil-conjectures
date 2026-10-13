## What changed

The target theorem now has a real proof that assembles two named intermediate results. Added `StandardSingleFlatCounitLocalizationData` for bounded termwise-flat stalk complexes and `StandardSingleFlatCounitLocalizationCompletion` for the derived scalar-extension/counit data and homology compatibility. Both intermediate proofs remain explicit named `sorry`s.

## Proved and sorry left

`standardSingleFlatCounit_localization` is proved by combining the two strict substatements. Sorry remains in `standardSingleFlatCounit_localization_data` (node `lem-pc-standard-single-flat-counit-localization-data`) and `standardSingleFlatCounit_localization_completion` (node `lem-pc-standard-single-flat-counit-localization-completion`).

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The original three-step plan had no single usable declaration for either the stalk-complex construction or the derived counit transport. These are split into two strict intermediate theorems so the target proof is fully assembled.

## New nodes

`lem-pc-standard-single-flat-counit-localization-data` and `lem-pc-standard-single-flat-counit-localization-completion` record the two intermediate obligations.

## Earlier second reading (a previous round; superseded)

The item module compiles with the two strict intermediate statements. The target signature is unchanged, and each added statement is a proper subproblem: one supplies only the stalk complex, while the other supplies the remaining derived data conditional on that complex.

## Second reading by R4

1. Compared the delivered localization module with the repository version; the target theorem signature is byte-for-byte unchanged, and only its proof and proof imports changed.
2. Compiled all delivered modules with `lcompile.py --all`; compilation succeeds. The two split statements retain `sorry` only in named theorems with corresponding DAG nodes; no definitions contain `sorry`, and no forbidden axioms or unsafe declarations were added.
3. Checked the split statements against the target: the data theorem supplies only the bounded termwise-flat stalk complex, while the completion theorem supplies the remaining derived counit package for a fixed complex, so each is strictly simpler and true by the cited localization argument.
4. Checked pruning and imports: the target keeps the presentation module public and uses the two proof-only imports; no old proof dependency is removed because the new route delegates to the split obligations.
5. Checked the unit record: the target remains the realizing node for `sk-thm-picard-coherence`; the decomposition follows the original localization steps and preserves that route.

Changed the target proof to apply the two named intermediate theorems, and added their modules and DAG nodes.
