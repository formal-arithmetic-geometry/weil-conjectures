## What changed

Added `SmoothAtPrimeFieldExtensionDescentAux`, splitting off the formal-smoothness-at-the-contracted-local-ring step. The target theorem now obtains this local formal smoothness and applies Mathlib's `Algebra.IsSmoothAt.exists_notMem_smooth` criterion. Added the corresponding DAG node.

## Proved and sorry left

`Algebra.isSmoothAtPrime_of_fieldExtension` is proved from the auxiliary declaration. `Algebra.formallySmoothAtPrime_of_fieldExtension` remains `sorry` as the faithful-flat cotangent descent subproblem.

## No longer needed

The long planned cotangent-localization dependency list is not imported by the delivered proof; only `Mathlib.RingTheory.Smooth.Locus`, `Sheaf.RingTheory.SingularIdeal`, and the auxiliary module are needed by the proof route.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan expands the full cotangent descent argument, but Mathlib already provides the final local criterion (`Algebra.IsSmoothAt.exists_notMem_smooth`). The remaining descent step is isolated as a single strict intermediate theorem.

## New nodes

`lem-weil-pbc-formally-smooth-at-prime-field-extension-descent` records the local formal-smoothness descent theorem used by the target.

## Second reading by C1

1. Compared both delivered modules with the repository versions. The existing target theorem's signature is unchanged byte for byte; the auxiliary theorem is a new split-off declaration. Verdict: pass.
2. Compiled both modules with `lcompile.py`; there are no errors, no forbidden declarations, and the only remaining `sorry` is the named auxiliary theorem. The target depends on `sorryAx` only through that explicitly split theorem. Verdict: pass.
3. Checked the auxiliary statement against the original descent statement and Stacks 00TG/02UQ. It is a strict intermediate formal-smoothness conclusion, with the same hypotheses and contracted prime, and is not a duplicate found by search. Verdict: pass.
4. Confirmed the proof uses Mathlib's `Algebra.IsSmoothAt.exists_notMem_smooth` criterion and keeps the unit route by retaining the formal-smoothness descent node. The target's old unused cotangent imports are pruned from its proof dependency list. Verdict: pass.
5. Updated both DAG nodes so their proof steps and `proof_deps` match the delivered route; the auxiliary node records the faithful-flat cotangent descent source and dependencies. Verdict: pass.

Changed the two proof implementations to use `haveI` (removing style warnings), wrapped the long auxiliary statement line, and synchronized the DAG proof metadata with the Lean proofs. No declarations or definitions were otherwise changed.

The second reading also removed the now-unused proof-only import `Sheaf.RingTheory.FiniteProjectivePrimeLocalFree` from the target module.
