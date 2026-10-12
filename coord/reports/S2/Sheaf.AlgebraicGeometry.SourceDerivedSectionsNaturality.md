## What changed

The target module now imports `SourceDerivedSectionsNaturalityCore` and proves
`AlgebraicGeometry.Etale.sourceDerivedSections_naturality` by pasting the
localization and evaluation squares. The new core module states the two strict
subcomputations and their categorical pasting theorem, which is proved from those
two subcomputations.

## Proved and sorry left

The target declaration `sourceDerivedSections_naturality` and the intermediate
declaration `sourceDerivedSections_naturality_compose` are proved. The new
declarations `sourceDerivedSections_naturality_core` and
`sourceDerivedSections_naturality_evaluation` remain `sorry`; each has a DAG node.

## No longer needed

No imports from the original module were removed. The proof uses only
`StrictLocalInjectiveSourceComparison` and the new core module.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped after observing that the component comparison maps
have no ready-made naturality theorem. The required reduction is to state the
localization square, the evaluation square, and their pasting as named
intermediate results.

## New nodes

Added `lem-weil-pbc-source-derived-sections-naturality-core`,
`lem-weil-pbc-source-derived-sections-naturality-evaluation`, and
`lem-weil-pbc-source-derived-sections-naturality-compose` in the sandbox DAG.

## Earlier second reading (a previous round; superseded)

A second reading is requested for the three new nodes and the target module. The
pasting proof compiles, preserves the target signature, and leaves only the three
strictly lower naturality/composition statements as named holes.

## Second reading by S2

1. I compared the delivered target module with the repository version. Its target
   signature is unchanged byte for byte; the only target change is replacing its
   proof with an application of the composition theorem. The added core module is
   the module named by the three split nodes.
2. I compiled both modules with `lcompile.py --all`. They compile without errors.
   The only remaining `sorry`s are the two genuinely lower naturality statements
   `sourceDerivedSections_naturality_core` and
   `sourceDerivedSections_naturality_evaluation`; the composition statement is now
   proved by categorical pasting. No definition contains `sorry`, and no forbidden
   declarations were added.
3. The two remaining split statements are strict subcomputations of the target:
   localization naturality and evaluation naturality. They are true by the
   cocycle/Yoneda calculations documented in their docstrings and have matching
   DAG nodes. The composition statement was checked as a derived pasting lemma,
   rather than left as a duplicate hole.
4. The target proof follows the unit route through the localization and evaluation
   squares, then pastes them. No import was removed; the proof-only core import is
   private. The three node records agree with the declarations and proof route.
5. I found no statement or definition change, no hollow definition, and no
   accidental weakening. I changed only the composition proof and this report.
