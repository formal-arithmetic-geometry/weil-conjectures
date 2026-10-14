## What changed

Added the proof import and closed the pullback clause of `moduleCup_pullback_naturality` by reducing arbitrary cohomology classes to cycles in a computing cup resolution. Added `Sheaf.Paper.ModuleCupPullbackCycleStep`, whose cycle-level theorem is the remaining resolution argument and is intentionally left for the next worker.

## Proved and sorry left

Closed the existing holes `moduleCup_coefficient_naturality` and
`moduleCup_pullback_naturality` in `CechCupPullbackCompat.lean`. The pullback proof uses the
strictly smaller `moduleCup_pullback_cycle_step` theorem. The latter is the only hole added and
remains `sorry` in `ModuleCupPullbackCycleStep.lean`, with node
`lem-sc-module-cup-pullback-cycle-step`.

## No longer needed

None. All prior proof imports remain used by the existing declarations.

## Where the brief, the DAG or earlier work was wrong

The DAG treated the pullback cup argument as a single direct theorem; the Lean interfaces expose the resolution-level cycle argument as a separate necessary step. No statement was weakened.

## New nodes

`lem-sc-module-cup-pullback-cycle-step` records the resolution-level cycle compatibility theorem and its source. Its module is `lean/Sheaf/Paper/ModuleCupPullbackCycleStep.lean`.

## Earlier second reading (a previous round; superseded)

The new cycle-level statement is strictly a resolution-level restriction of the remaining pullback theorem. The main theorem now obtains representatives using the existing surjectivity lemma and invokes only this smaller statement; no target signature changed.

## Second reading by W2

1. Compared `CechCupPullbackCompat.lean` with the repository version. Existing declaration
   signatures and definitions are unchanged; only proof imports, local proof lemmas, and proofs
   differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. The main module and the new cycle
   module compile without errors. The only remaining `sorry` is the named theorem
   `moduleCup_pullback_cycle_step`; it has the matching split node and a source/docstring proof.
   No forbidden declarations or hollow definitions were added. Verdict: pass.
3. Checked the split theorem against the cycle-level resolution statement. It is strictly smaller
   than `moduleCup_pullback_naturality`, retains the required hypotheses and conclusion, and has
   no duplicate declaration in the library. Verdict: pass.
4. The proof reduces coefficient naturality to simultaneous resolution maps, and pullback
   naturality to cycle representatives plus the split theorem. The existing unit route remains
   represented by the comparison and resolution nodes; no unused import was found. Verdict: pass.
5. The DAG node for `moduleCup_pullback_cycle_step` matches the Lean declaration, including its
   proof dependency and `split` status. Verdict: pass.

Changed the new cycle module's `ModuleCupPairingExists` import to `public import`, since
`CupResolutionPairing` occurs in its public theorem signatures. No theorem statements changed.
