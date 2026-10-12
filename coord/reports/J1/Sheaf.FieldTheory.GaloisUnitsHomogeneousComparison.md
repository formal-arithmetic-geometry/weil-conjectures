## What changed

Added `Sheaf.FieldTheory.GaloisUnitsHomogeneousCocycleDescent` with two intermediate declarations. The assigned theorem is proved by applying the descent theorem to the homogeneous/inhomogeneous cocycle equivalence. The new module is imported proof-only.

## Proved and sorry left

The assigned declaration `Field.nonempty_equiv_galoisUnitsH2_twoCocycleClasses` is proved. Two strictly lower intermediate declarations remain sorry: `Field.nonempty_equiv_galoisUnitsHomogeneousCocycles_twoCocycle` and `Field.nonempty_equiv_galoisUnitsH2_twoCocycleClasses_of_cocycle_equiv`, with nodes `lem-sc-galois-units-homogeneous-cocycle-equivalence` and `lem-sc-galois-units-homogeneous-cocycle-descent`.

## No longer needed

No stated imports or DAG dependencies were pruned; both cohomology and explicit cocycle definitions are used by the new intermediate module.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan suppresses the substantial cochain change-of-variables and quotient descent. These are represented as two strictly simpler intermediate statements.

## New nodes

`lem-sc-galois-units-homogeneous-cocycle-equivalence` records the degree-two cocycle equivalence. `lem-sc-galois-units-homogeneous-cocycle-descent` records its descent through topological-module homology to the coboundary quotient.

## Earlier second reading (a previous round; superseded)

The decomposition is checked against the assigned signature: the upper theorem is obtained by a real application of the descent statement, while the two remaining declarations are strictly lower cocycle and quotient steps. The unit route is retained.

## Second reading by J1

1. Compared `GaloisUnitsHomogeneousComparison.lean` with the repository version. The existing target declaration has the same signature byte for byte; only its proof and the proof-only import were added. Verdict: pass.

2. Compiled both delivered modules with `lcompile.py --all`. They compile without errors. The target is proved; the two explicitly named intermediate declarations remain the only `sorry`s, and neither is in a definition. Verdict: pass.

3. Checked the two added DAG nodes and searched the library and Mathlib for an existing declaration. The intermediate claims are strictly below the target and correspond to the two actual mathematical steps, though their proofs remain open. Verdict: pass for the decomposition.

4. The target proof follows the descent route and retains the cohomology and explicit cocycle imports. The comparison module's added import is proof-only. Verdict: pass; no imports or old proof dependencies can be pruned from the delivered route.

5. The delivered node metadata agrees with the declarations and the unit `sk-thm-br` route is unchanged. Verdict: pass.

Changed after review: no Lean declarations or statements were changed. Added this second-reading record only. The descent intermediate's prose explicitly records that boundary compatibility is part of the mathematical argument; its Lean hypothesis currently packages only the cocycle equivalence, so this remains an open proof obligation rather than a claimed completed derivation.
