## What changed

Proved `Algebra.Presentation.localized_conormal_basis_jacobian` in
`Sheaf.RingTheory.LocalizedConormalBasisJacobian`, preserving its full signature and visibility.
Localized ideal membership is proved directly: span induction lifts conormal combinations into
the initial-relation ideal; Mathlib localized submodules clear two powers of the localization
parameter; equality of conormal classes puts the difference in the square of the kernel.
The image of that power is a unit in the polynomial localization and can be cancelled.
In fact this part proves membership for every relation, without using the index lower bound.

For the matrix conclusion, the existing
`Algebra.Generators.principal_localization_naive_cotangent` supplies injectivity and cokernel
comparison. Smoothness identifies that cokernel with a projective module of differentials.
Mathlib splits the differential, computes its matrix in the prescribed conormal basis and the
polynomial differential basis, and turns composition of the linear maps into matrix multiplication.
This follows the already proved splitting argument in `PresentationLocalizedConormalSplit`,
without importing that module or changing it.

Added proof-only imports of `Sheaf.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent`,
`Mathlib.LinearAlgebra.Matrix.ToLin`, `Mathlib.Algebra.Module.LocalizedModule.Submodule`, and
`Mathlib.RingTheory.Localization.BaseChange`. No public import, definition, or statement changed.
Updated only the existing node's `proof`, `proof_deps`, and `proof_origin` to match the Lean route.
The argument makes no nontrivial-ring assumption and handles c=0, n=0 and zero localizations.
The source passage was checked at https://stacks.math.columbia.edu/tag/07EZ, proof (e).

## Proved and sorry left

Closed the sole hole: `Algebra.Presentation.localized_conormal_basis_jacobian`
(node `lem-weil-pbc-localized-conormal-basis-jacobian`).
There are no remaining sorries in this module, no new modules, and no added holes.
This is a proof from existing statements, not a decomposition into new statements.
The existing dependency `Algebra.Generators.principal_localization_naive_cotangent` still has
its own sorry in the library; this delivery neither proves nor changes that separate item.
Local compilation succeeded without warnings; the delivery dry run is the final validation.

## No longer needed

Removed the proof-only import `Sheaf.RingTheory.SmoothLocalizationConormalSplit` and the proof
edge to `lem-weil-pbc-smooth-localization-conormal-split`. Its bundled quotient presentation,
localized-module transport, Kahler projection and product equivalence are not needed by this proof.
In particular this route does not use `Sheaf.RingTheory.JacobiZariskiQuotientSmooth`
(node `lem-weil-pbc-jacobi-zariski-quotient-smooth`), which was imported by that removed module.
These are pruning opportunities on this route; other target branches may still use them.
`Sheaf.RingTheory.PresentationLocalizedConormalSplit` was read for its existing proof pattern
but is not imported or a dependency of the resulting proof.
All retained and added imports serve statements, definitions or the proof.
No realized statement or step of `dag/units/sk-thm-p1.json` was bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned quotient-to-A transport through `P.quotientEquiv` is unnecessary: the existing
principal-localization theorem works directly with the original presentation and both universes.
The original theorem docstring's final transport sentence describes the earlier route;
the new node proof records the implemented route. The mathematical statement is unchanged.
There was no false statement, forced adaptation, interface change, or tool workaround.

## Second reading by A2

1. **Visible changes:** Compared the delivered module and node with the repository versions.
   The theorem signature and all existing declarations are byte-for-byte unchanged; only the
   proof, proof-only imports, proof route metadata, and proof docstring changed.
2. **Proof validity:** Compiled the module with `lcompile.py`; it has no errors, warnings,
   forbidden declarations, or `sorry`. A scratch `#print axioms` shows only the permitted axioms
   plus `sorryAx` inherited from the existing principal-localization dependency.
3. **Statements and nodes:** The target statement is unchanged and no split-off statements or
   nodes were added. The existing node's proof steps, dependencies, and origin now match the
   direct principal-localization and matrix proof in Lean.
4. **Pruning and imports:** The removed smooth-conormal-split import and dependency are unused;
   all retained imports are used by the statement or proof. The unit route remains realized.
5. **Source and edge cases:** The proof follows the cited Stacks Tag 07EZ argument and handles
   empty bases, zero localization, and zero indices without extra assumptions. No hollow
   definitions or data selected from an undetermined existence theorem occur.

Changed the stale proof docstring so it describes the implemented principal-localization
cotangent comparison rather than the earlier quotient-transport route.
