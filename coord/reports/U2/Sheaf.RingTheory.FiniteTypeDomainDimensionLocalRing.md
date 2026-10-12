## What changed

Added two proof-only intermediate modules and imported them into the target module. The target theorem now combines the two component theorems by conjunction.

## Proved and sorry left

Closed the original target declaration `finiteTypeDomain_ringKrullDim_localizationAtMaximal` by a genuine conjunction proof. Two strictly smaller intermediate declarations remain with `sorry`: `finiteTypeDomain_ringKrullDim_localizationAtMaximal_localization` and `finiteTypeDomain_ringKrullDim_localizationAtMaximal_chains`, with DAG nodes recorded below.

## No longer needed

The target module no longer imports `Sheaf.RingTheory.PolynomialRingMaximalChainHeightDifference`
or `Sheaf.RingTheory.PolynomialRingMaximalLocalizationDimension`: those dependencies belong to
the two split component statements, whose modules retain the needed plan imports.  The target
node's direct proof dependencies were pruned to the two component nodes.

## Where the brief, the DAG or earlier work was wrong

No statement or definition was changed. The DAG plan requires substantial commutative algebra unavailable in the current library, so it was split into the two component claims above.

## New nodes

`lem-weil-pbc-finite-type-domain-dimension-local-ring-localization` records the localization equality component.

`lem-weil-pbc-finite-type-domain-dimension-local-ring-chains` records the natural-number dimension and common maximal-chain length component.

## Earlier second reading (a previous round; superseded)

The target signature is unchanged. The two new declarations are strict components of the target conjunction, and their statements match their Lean signatures and DAG nodes. The conjunction proof compiles with lcompile.py; the remaining sorries are exactly the two component claims. The unit route is preserved at the target level.

## Second reading by U2

1. **Visible changes.** Compared with the repository module, the target theorem has the same
   signature and only its proof is filled in. The two component modules and their DAG nodes are
   new, and the target DAG proof now records the conjunction route. No existing declaration's
   statement or definition was changed.

2. **Compilation and proof checks.** `lcompile.py --all` compiles all three modules without
   errors or warnings. The only remaining `sorry`s are the two explicitly named component
   theorems; there are no `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions.

3. **Statements.** Each split statement is a genuine conjunct of the original target, with the
   same hypotheses and conclusion, and is strictly smaller than the conjunction. The statements
   agree byte-for-byte with the declarations and with their new DAG nodes. No existing library
   theorem matching either statement was found in the recorded searches.

4. **Route and pruning.** The target proof applies the two component declarations directly,
   preserving the unit's target route. The target's obsolete polynomial imports and direct DAG
   dependencies were removed; the component modules retain the mathematical dependencies needed
   by their planned proofs.

5. **Axioms and edge cases.** The conjunction proof introduces no axioms beyond those allowed by
   the project. The split statements retain the original field, finite-type, commutative-ring,
   and domain hypotheses, including the zero-dimensional cases, so no edge case is weakened.

I changed only the target proof/dependency record, corrected the two component docstrings and
removed two now-unused target imports. The two component theorem proofs remain open because the
required finite-type dimension and height results are not available in the current library.
