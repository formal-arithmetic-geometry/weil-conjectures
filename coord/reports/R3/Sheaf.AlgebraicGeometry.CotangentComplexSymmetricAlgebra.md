## What changed

Completed `AlgebraicGeometry.cotangentComplex_symmetricAlgebra` in
`Sheaf.AlgebraicGeometry.CotangentComplexSymmetricAlgebra`, preserving its signature,
visibility, and existing docstring. The presentation is obtained from
`symmetricAlgebra_quotient_module` and Mathlib's standard-basis polynomial equivalence.
The linear relation map is constructed explicitly, then extended by scalars;
Mathlib's cotangent spanning lemma proves surjectivity. The differential formula and
image equality are proved directly. Fully proved private helpers construct the final
differential equivalence by symmetric-algebra and differential universal properties.
They adapt the proof of `Sheaf.RingTheory.SymmetricAlgebraDifferentials` to independent
ring and module universes, without changing that module or exposing a duplicate API.
All helper definitions contain actual constructions and proved laws.

Added proof-only imports `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis` and
`Mathlib.Algebra.TrivSqZeroExt.Basic`. Removed the proof-only finite-presentation import.
Updated the existing DAG node's proof, proof dependencies, and proof origin to match
this argument. No other public interface or module changed; no new nodes or holes.
The node is below the unit's realized statements and steps, so the unit route is retained.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.cotangentComplex_symmetricAlgebra`
(node `lem-weil-pbc-cotangent-complex-symmetric-algebra`). Every private helper is proved.
No `sorry` remains in the delivered module, and no hole is added or split off.

The imported existing `symmetricAlgebra_quotient_module`
(node `lem-weil-pbc-symmetric-algebra-quotient-module`) is now proved in the repository
from `symmetricAlgebra_quotient_module_kernel`, whose module still contains a `sorry`
(node `lem-weil-pbc-symmetric-algebra-quotient-module-kernel`). This delivery proves
the assigned theorem from the existing quotient-module dependency; it does not claim
a transitive sorry-free proof. The differential equivalence itself
uses only proved Mathlib facts. The proof is uniform for the zero ring, zero module,
empty index set `Fin 0`, nonfree modules and noninjective conormal maps.

## No longer needed

Removed import `Sheaf.RingTheory.SymmetricAlgebraFinitePresentation` and its direct
proof dependency `lem-weil-pbc-symmetric-algebra-finite-presentation`: surjectivity
already follows from the quotient-module theorem, with no finite-presentation assumption.

Removed from this node's proof dependencies:
- `lem-weil-pbc-jacobi-zariski-differential-maps`: no cokernel/exact-sequence argument.
- `lem-weil-pbc-polynomial-ring-kahler-basis`: linearity of D computes the displayed formula.
- `lem-weil-pbc-tensor-right-exact`: the differential equivalence is constructed by
  universal properties instead of tensoring an exact sequence.

These Mathlib leaves have no separate Sheaf module to remove here. Existing public
imports and statement dependencies remain unchanged. The quotient-module dependency,
free-module polynomial equivalence, symmetric universal property, base-change universal
property, and Kähler differential universal property remain needed. This is pruning
from the assigned node, not a claim that other target branches no longer need these nodes.

## Where the brief, the DAG or earlier work was wrong

The DAG plan is valid, but stronger tools than necessary were suggested for the last
three calculations. The direct universal-property proof eliminates the cokernel route.
The existing `symmetric_algebra_differentials` theorem puts its ring and module in one
universe and was absent from the local compiled snapshot at inspection; its construction
was adapted in proved private helpers to preserve the assigned theorem's independent
universes. No unavailable declaration was restated as a new public theorem or hole.
The known false injectivity assertion from Stacks 07EV is neither assumed nor proved.

Validation: the prescribed `deliver3.py --no-push` dry run compiled the complete
module, ran its axiom probe, and printed OK. The preflight passed except for the
second-reading section, which the independent reader writes. There are no interface
changes, no warnings, and no textual holes. Nothing was pushed.

## Second reading by R3

1. **Statements and accidental changes.** Compared the delivered module with the
repository version. The target theorem signature, visibility, docstring, and all
existing declarations are unchanged; only proof imports, private proof helpers, and
the proof body differ. The DAG node's statement is unchanged.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds with no
errors or warnings. Searched the delivered files for `sorry`, `axiom`, `unsafe`,
`opaque`, `extern`, and `implemented_by`; none occur. The proof uses constructions
and universal properties only, and the delivery axiom probe reports no impermissible
axioms.

3. **Truth and strength of statements.** The existing corrected statement is the
surjective conormal assertion plus the differential and symmetric-algebra
Kähler-differential conclusions, so it avoids the false injectivity claim in Stacks
07EV. Every private helper is a strictly internal construction used to prove that
statement; no new public theorem or hole was added. The zero-ring, zero-module,
empty-index, nonfree, and noninjective cases are covered by the universal-property
proof.

4. **Shortest route and pruning.** The proof uses Mathlib's symmetric-algebra basis,
quotient-module, cotangent, and Kähler universal-property lemmas. It removes the
finite-presentation, Jacobi–Zariski, polynomial-basis, and tensor-right-exact imports
and dependencies that are unnecessary for this direct route; the node's proof and
`proof_deps` record those changes.

5. **Unit route and DAG agreement.** The unit's realized statement and steps remain
the route: the quotient presentation, conormal generation, differential computation,
and symmetric-algebra differential equivalence are all present. The node's proof,
dependencies, origin, and Lean declaration agree with the delivered code. No new
nodes or split-off holes were required.

Changed during this second reading: appended this review section only. No Lean code,
node, or imports required repair.

The earlier attempt stopped at a launcher/check-out mismatch involving the missing
`import_cycles.refuse_missing` function. The current prescribed dry run passes that
check without any tool modification or workaround. The existing proof was reviewed
against the unchanged statement and updated proof plan; no Lean repair was needed.
