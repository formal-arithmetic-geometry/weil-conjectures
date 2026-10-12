## What changed

Replaced the expensive direct categorical proof in `exists_degreewise_of_stalk_local_core` with a finite intersection reduction. The theorem constructs the finite degree interval and supplies zero witnesses outside it, then applies `exists_degreewise_finite_aux`. Added the new proof-only module `FiniteFreeStalkDegreewiseLiftAux` containing that split-off intermediate theorem. The pre-existing `FiniteFreeStalkDegreewiseLift` module was restored unchanged; the attempted restriction helper was removed because the core proof does not use it.

## Proved and sorry left

The target `exists_degreewise_of_stalk_local_core` is proved. `exists_degreewise_finite_aux` remains sorry-backed, with its finite-gluing obligation documented in its docstring and node `lem-pc-finite-free-stalk-degreewise-lift-core-aux`. No other declarations or definitions were added.

## No longer needed

The old direct categorical transport helpers and their `DerivedPullback` import are no longer needed by the target proof. The attempted `restrict_degreewise_of_stalk_local` declaration and its module replacement were removed because they were unused and would have changed the existing `FiniteFreeStalkDegreewiseLift` interface.

## Where the brief, the DAG or earlier work was wrong

The original direct proof exceeded the compiler time limit because elaborating nested categorical transport helpers was too expensive. The finite intersection argument is a valid shorter route once the finite gluing step is split into its own theorem. The earlier delivery also incorrectly replaced the existing `FiniteFreeStalkDegreewiseLift` module with an unrelated helper; this reading restored that module and kept only the genuinely used auxiliary theorem.

## Second reading by E3

1. Compared the delivered core module with the repository version. The target declaration signature is byte-for-byte unchanged; only its proof and proof-only imports changed. The existing `FiniteFreeStalkDegreewiseLift` module is unchanged.
2. Compiled all sandbox modules with `lcompile.py`; compilation succeeds without warnings after line wrapping. The only remaining `sorry` is the named `exists_degreewise_finite_aux` theorem, with a docstring and DAG node. No definitions contain `sorry`, and no forbidden declarations occur.
3. Checked the split-off auxiliary statement against the finite-intersection argument. It is a strict lower-level reduction, has the required source, proof description, and node, and is used by the target. No duplicate theorem was found in the repository or Mathlib search results.
4. Confirmed the proof uses the interval `Finset.Icc`, the four strict-support zero lemmas, and `exists_degreewise_finite_aux`; the stale categorical route and unused attempted restriction helper were pruned. The unit route remains through the core node.
5. Updated the core node's `proof` and `proof_deps` to name the auxiliary node used by the Lean proof; the auxiliary node records its own declaration and source. Verdict: statements unchanged and DAG agrees with the delivered code.

## New nodes

`lem-pc-finite-free-stalk-degreewise-lift-core-aux` records the finite gluing intermediate theorem in `dag/nodes/sec-picard-framework/lem-pc-finite-free-stalk-degreewise-lift-core-aux.json`.
