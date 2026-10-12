## What changed

Proved `constantFiniteMatrixDualKernelIso_aux` by reducing the matrix map to a
natural finite-free dual-basis comparison, then applying `kernel.mapIso` and the
finite-limit preservation isomorphism for `constantSheaf`. Added the intermediate
module `Sheaf.ConstructibleSheaf.ConstantFiniteFreeDualNaturality`, whose theorem
is the only remaining sorry. Updated the item node proof and dependencies.

## Proved and sorry left

The item's `constantFiniteMatrixDualKernelIso_aux` is proved. The new theorem
`constantFiniteFreeDualNaturality` remains `sorry` in node
`lem-constant-finite-free-dual-naturality`; it is the strict finite-free
basis/naturality subargument used by the proof.

## No longer needed

No imports were removed. The original plan's informal finite-biproduct and
kernel steps are represented by the new intermediate theorem; no additional
nodes or modules are needed by this proof.

## Where the brief, the DAG or earlier work was wrong

The DAG had no Lean dependency for the finite-free dual-basis/naturality step.
It is therefore split into the named intermediate theorem above. The target
statement and all existing interfaces are unchanged.

## New nodes

`lem-constant-finite-free-dual-naturality` records the finite-free dual-basis
comparison and its naturality with respect to matrix maps. Its module is
`lean/Sheaf/ConstructibleSheaf/ConstantFiniteFreeDualNaturality.lean`.

## Earlier second reading (a previous round; superseded)

A second reader should check the new finite-free naturality node and the kernel
composition against the unchanged item statement.

## Second reading by Y2

1. **Module comparison:** Compared the delivered item module with the repository
   version. The existing theorem signature is byte-for-byte unchanged; only its
   proof and proof-only imports differ. Verdict: pass.
2. **Compilation and axioms:** Compiled both delivered modules with the launcher.
   The item compiles without errors; the sole remaining `sorry` is the named
   `constantFiniteFreeDualNaturality` split-off theorem. The target's remaining
   `sorryAx` dependency is exactly this open node. Verdict: pass.
3. **Statements and node:** Checked the split-off theorem against its DAG node.
   It is a strict finite-free dual/naturality substatement, has a source and a
   complete proof sketch, and is not duplicated in the library. Verdict: pass.
4. **Proof route and pruning:** The proof uses `kernel.mapIso` and the existing
   constant-sheaf kernel preservation isomorphism, with the finite-free step
   isolated in the new theorem. No listed proof dependency is unused, so no
   imports or nodes can be pruned. Verdict: pass.
5. **Unit route:** The construction retains the unit `sk-thm-p1` route and does
   not alter any target or existing interface. Verdict: pass.

Changed only the report by adding this review record; no Lean statement or
definition was changed during second reading.
