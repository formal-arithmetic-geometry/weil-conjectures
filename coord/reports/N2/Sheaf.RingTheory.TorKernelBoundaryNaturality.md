## What changed
Added two intermediate modules splitting the proof into an exactness family and a naturality coherence component. The target theorem now combines these statements.

## Proved and sorry left
`exists_tor_kernel_boundary_natural` is proved from the two intermediate declarations. `exists_tor_kernel_boundary_exact` remains sorry (node `lem-sc-p1-tor-kernel-boundary-exact`). `tor_kernel_boundary_naturality_of` remains sorry (node `lem-sc-p1-tor-kernel-boundary-naturality-of`).

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The stated plan requires a cross-presentation naturality construction absent from available library declarations, so it was split into a strict coherence intermediate theorem.

## New nodes
`lem-sc-p1-tor-kernel-boundary-exact` and `lem-sc-p1-tor-kernel-boundary-naturality-of`.

## Earlier second reading (a previous round; superseded)
The target proof combines the two strictly smaller intermediate statements; signatures are unchanged.

## Second reading by N2

1. Compared `Sheaf.RingTheory.TorKernelBoundaryNaturality.lean` with the repository copy. The
   target declaration signature is byte-for-byte unchanged; only its proof and proof-only imports
   differ. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds with no
   errors. The only remaining `sorry`s are the two explicitly named split-off theorems, and no
   forbidden declarations or hollow definitions were added. Verdict: pass.
3. Re-read the split statements and checked their edge cases and interfaces. The exactness node
   states only existence and the two exact pairs; the naturality node takes a family and its
   exactness as hypotheses and states only the commuting-square equality. Their docstrings cite
   Stacks Project Section 00LY and give the resolution and homology argument. Verdict: pass.
4. The proof uses the two strictly smaller split theorems and no shorter available Mathlib or
   library theorem was found. Removed the unused proof-only import
   `Sheaf.Algebra.Homology.FreeResolutionSesSplit` from the target module. Verdict: pass.
5. Updated both split-node `statement`, `proof`, and `proof_deps` fields to agree with the Lean
   declarations. The target unit route remains through the exactness and naturality components.
   Verdict: pass.

Changed the two split-node descriptions and proof metadata, expanded their proof docstrings, and
removed the unused target import. No target statement or definition changed.
