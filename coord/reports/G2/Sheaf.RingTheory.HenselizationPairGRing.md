## What changed

Added `HenselizationPairGRingCore` with a named intermediate theorem isolating the Noetherian and maximal-local regularity part of Tag 0AH3. The target theorem now combines this theorem with `isGRing_iff_maximalIdeal`, installs the resulting Noetherian instance, and concludes `IsGRing`.

## Proved and sorry left

`RingTheory.isGRing_of_pair_henselization` is proved. The intermediate theorem `RingTheory.henselization_pair_noetherian_and_maximal_regular` remains `sorry`; its node is `lem-weil-pbc-henselization-pair-g-ring-core`.

## No longer needed

Removed direct proof imports of `FiniteSeparableFibersOfEtaleColimit`, `FlatLocalCompletionIso`, `GRingMaximalIdealCriterion`, `GeometricRegularitySeparableExtension`, and `PairHenselizationNoetherianCompletion`; these are reached through the core theorem or its criterion import. The target proof uses the maximal-ideal criterion and the new core theorem.

## Where the brief, the DAG or earlier work was wrong

The original five-step proof cannot be completed from the current Lean interfaces without a substantial construction of localizations, completions, and fibre decompositions. I split the first four steps into one strictly smaller intermediate proposition and proved the final assembly in Lean.

## New nodes

`lem-weil-pbc-henselization-pair-g-ring-core` records the Noetherianity and maximal-local regularity intermediate proposition and its source in Tag 0AH3.

## Second reading by G2

1. Compared both delivered modules with the repository versions. The target theorem
   signature and all existing declarations are unchanged byte for byte; the only
   new declaration is the explicitly split intermediate theorem.
2. Compiled both modules with `lcompile.py --all`. There are no errors, forbidden
   declarations, or unlisted sorries. The sole remaining sorry is the named core
   theorem, whose node and docstring are present. The target proof uses only the
   permitted standard axioms apart from that open theorem.
3. Checked the split statement against the target: it supplies exactly
   Noetherianity and regularity at every maximal ideal, which the maximal-ideal
   criterion consumes. It is strictly smaller than the target and has a source,
   proof plan, node, and recorded searches; no duplicate library theorem was found.
4. Checked pruning and imports. The parent retains its public statement imports and
   privately imports the core proof module; the five former direct proof imports
   are removed and listed above. The target node's proof dependencies now match
   the core theorem and maximal-ideal criterion, and the unit route through
   `sk-thm-p1` is retained.
5. Checked DAG consistency: the target and core node declarations, statements,
   proof dependencies, origins, chapter, and unit agree with the Lean files.

Changed the target proof's local Noetherian instance from `letI` to a class-typed
`let`, removing the style warning while preserving elaboration. No statements or
definitions were changed.
