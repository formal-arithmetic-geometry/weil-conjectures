## What changed

Added the proof-only import Sheaf.ConstructibleSheaf.ConstantFiniteDual and proved
AlgebraicGeometry.Scheme.nonempty_constantModuleDualIso by its existing declaration
AlgebraicGeometry.Scheme.nonempty_constant_finite_dual_iso. The signatures agree exactly.
Updated lem-weil-pbc-constant-module-dual to record the dependency actually used.
No signature or definition changed. No new module or theorem was introduced.

## Proved and sorry left

Closed the single local hole in AlgebraicGeometry.Scheme.nonempty_constantModuleDualIso
(lem-weil-pbc-constant-module-dual). No sorry remains in the item's module; zero holes added.
The proof depends on the existing sorry in
AlgebraicGeometry.Scheme.nonempty_constant_finite_dual_iso
(lem-weil-pbc-constant-finite-dual), which is an existing identical interface, not a new
restatement. This deduplicates the proof obligation; it does not finish the finite
presentation argument or claim that the result is independent of sorryAx.

## No longer needed

No imports removed, and no named nodes or modules pruned. The independent three-step
finite-presentation proof planned for lem-weil-pbc-constant-module-dual is unnecessary:
the same argument is already assigned to lem-weil-pbc-constant-finite-dual.
The unit sk-thm-p1 does not list either node as a realized statement or proof step;
its route is preserved.

## Where the brief, the DAG or earlier work was wrong

Two pre-existing nodes and modules state exactly the same constant-module dual theorem.
They were introduced by separate reductions of DualStalk and DualLocallyConstant.
The existing declaration can serve both. Local compilation initially failed because
ConstantFiniteDual.olean was missing from the last green build cache; the worker rules
require waiting for refresh rather than recreating it.

Validation: lcompile.py and deliver3.py --no-push both pass when the unchanged
ConstantFiniteDual source is present in the sandbox import closure. The source is an
exact mirror of the repository module and deliver3.py includes no changed dependency
content in the resulting commit.

## Second reading by G1

1. Compared `ConstantModuleDual.lean` with the repository version. The theorem
   signature and all existing declarations are unchanged; the only change is the
   proof-only import and proof body.
2. Compiled both sandbox modules with `lcompile.py --all`; compilation succeeds. The
   proof introduces no `sorry`, axiom, unsafe declaration, or hollow definition. The
   theorem is a direct application of the existing finite-dual interface.
3. The imported theorem has exactly the same hypotheses and conclusion after
   instantiation (`X` and `M`), so no new statement was split off and no statement was
   weakened or strengthened.
4. The proof takes the shortest available route by reusing
   `nonempty_constant_finite_dual_iso`; no imports or nodes can be pruned from the
   delivered module, and the unit route remains unchanged.
5. The DAG node proof and `proof_deps` name exactly that declaration, matching the Lean
   proof and preserving the unit metadata.

Changed only the report by adding this second-reading record; no Lean statement or
definition was altered.
