## What changed

Corrected the module docstring: it has no mathematical imports, but it does import
Mathlib.Init for the build probe. No declarations, signatures, or proofs changed. The assigned module is already a retired compatibility module,
with only the infrastructure import Mathlib.Init and no declarations. Its sandbox copy compiles successfully with lcompile.py.

## Proved and sorry left

Zero holes present at assignment: zero closed, zero added, zero left.
The canonical declaration
AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf
is already proved in Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf.
The node lem-weil-pbc-torsor-equivariant-presheaf-sheaf already points to that
canonical module and records its proof review on 2026-10-14.

## No longer needed

No imports removed by this delivery. No new pruning claimed. The duplicate
mathematical interface of Sheaf.ConstructibleSheaf.TorsorEquivariantPresheafSheaf
was already retired before this assignment. Keep the canonical theorem and its
existing proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The dispatcher brief says this module still contains sorry; the supplied current
repository file has neither a theorem nor a sorry. The node's lean.module is
Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf, not the assigned module.
There is no remaining proof work in the assigned file, and no new proof or
pruning progress is claimed.

## Second reading by F2

1. Compared the delivered module with the repository version. The only change is
   its explanatory module docstring and the retained `Mathlib.Init` build-probe
   import; there are no declarations, signatures, definitions, or target
   statements changed. Verdict: pass.
2. Compiled the module with `lcompile.py` and checked that it contains no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The
   retired module has no declarations whose proof axioms need auditing; the
   retained theorem is in the canonical module named above. Verdict: pass.
3. Checked the DAG node and canonical declaration. The assigned file is a
   compatibility module, while the node deliberately points to
   `equivariantModulePresheaf_isSheaf` in
   `TorsorEquivariantModuleIsSheaf`; no split-off statement is introduced and
   no existing statement is restated. Verdict: pass.
4. Checked the proof route and imports. Since this file has no mathematical
   content, there is no shorter proof or import pruning available here; the
   canonical theorem and its dependencies remain in their existing module.
   Verdict: pass.
5. Checked the unit route and DAG metadata. The unit's realized route remains
   attached to the canonical theorem, and this compatibility module does not
   bypass or alter it. Verdict: pass.

Changed only the module documentation to accurately describe the retained
infrastructure import and the retired interface; no mathematical code or DAG
record required modification.
