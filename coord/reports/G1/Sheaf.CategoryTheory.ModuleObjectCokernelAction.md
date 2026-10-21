## What changed

Proved `CategoryTheory.Mod.exists_cokernel_action` in
`Sheaf.CategoryTheory.ModuleObjectCokernelAction`, starting from the current
repository file restored by commit `45eba2ae8c4`. Compared that file with the
retained delivery: the signature, imports and docstrings are identical; the only
Lean change replaces its `sorry` with the complete retained proof.

The proof follows all seven steps of `lem-sfb-modobj-cokernels`. It maps the
supplied cokernel through `tensorLeft R` twice, descends the action, proves its
unit and associativity laws by epimorphism cancellation, and constructs the
module-category cokernel with its factorization and uniqueness proofs. Action
uniqueness is established among all underlying maps. No new declarations,
intermediate holes, node changes, or consumer adaptations are needed.

The retained searches found `CokernelCofork.mapIsColimit` and the analogous
chosen-cokernel construction in
`WeilConjectures.CategoryTheory.ModuleObjects.Abelian`. The proof for the supplied
arbitrary cokernel uses preservation of that cofork twice, rather than assuming
preservation of arbitrary epimorphisms.

Change record: `coord/changes/module-object-cokernel-action.md`, updated to refer
to the current existing module rather than its obsolete absent-file base.

## Proved and sorry left

Closed `CategoryTheory.Mod.exists_cokernel_action`
(node `lem-sfb-modobj-cokernels`): one of one holes proved, zero holes added,
zero split off, zero remaining.

The repaired sandbox file passed single-file `lcompile.py` with no errors or
warnings. The delivery tool additionally compiles its generated axiom probe.

## No longer needed

None. No imports, nodes or modules are removed. The declared dependency
`sk-def-sfb-module-objects` is realized by the imported Mathlib module-object
structures and axioms and remains used. All seven DAG steps and the unit route
are preserved.

## Where the brief, the DAG or earlier work was wrong

The prior delivery was based on `185674722`, which lacked the module subsequently
created by `45eba2ae8c4`. The landing tool returned it at `b6291f17e6d` for this
base mismatch. This repair reads the current repository source, verifies its
interface against the retained work, applies the proof to that current source,
and recompiles it. The earlier change record's claim that the delivery adds a
module is obsolete and has been corrected. No mathematical discrepancy was
found in the statement or the seven-step DAG proof.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
