## What changed

Proved `IsDiscreteValuationRing.lattice_distance_determinant` without changing its
statement or any public definition. Three proved private helpers implement the
Smith normal form quotient-length calculation, compatibility of lattice coordinates
with extension to the fraction field, and the length formula for an inclusion of
full lattices. The main proof applies that formula directly to the intersection
lattice and compares two ambient automorphisms using determinant multiplicativity.
The node copy records this shorter route.

## Proved and sorry left

Closed the single original hole in
`IsDiscreteValuationRing.lattice_distance_determinant`
(node `lem-exc-dvr-lattice-distance-determinant`). No holes added or split off.
The delivered module has zero `sorry` occurrences. The private helpers
`length_quotient_eq_ord`, `extend_repr`, and `lattice_inclusion_length` are proved
from Mathlib. The required `deliver3.py --no-push` dry run compiled the complete
module and passed preflight, including its axiom checks.

## No longer needed

Removed the proof import
`WeilConjectures.LinearAlgebra.Matrix.CauchyBinet` and the dependency
`lem-weil-pbc-cauchy-binet` (including its obsolete top-level `tool_uses` entry):
square determinant multiplicativity already exists in
Mathlib. The explicit uniformizer argument and dependency
`lem-weil-pbc-dvr-unit-times-uniformizer-power` are unnecessary because
`Ring.ord`, `Ring.ord_mul'`, `Ring.ordFrac_eq_ord`, and the finite-order API
already provide the required cyclic length and valuation identities.

Also removed the redundant direct proof imports
`Mathlib.LinearAlgebra.FreeModule.PID`,
`Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, and
`Mathlib.RingTheory.PrincipalIdealDomain`: the preserved public determinant import
and the two new proof imports (`Mathlib.LinearAlgebra.FreeModule.Finite.Quotient`
and `Mathlib.Algebra.Module.Lattice`) supply their used APIs.

The original plan's smaller common sublattice and its quotient cancellation
(steps 4, 8 and 9) are unnecessary: Mathlib proves that the intersection is itself
a full lattice, and the proof computes the two desired quotients directly. Smith
normal form, freeness, finite-product length additivity, determinant and length
definitions, and DVR Noetherianity remain used. No unit statement or realized
proof step is bypassed; `sk-prop-a1-kummer` has no realized nodes for this item.
No global pruning claim is made for modules that other items may still use.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The nine-step handwritten plan omitted the
existing Mathlib full-lattice intersection and coordinate quotient APIs, which
avoid a separate denominator-clearing construction and common-quotient argument.
The retained Smith normal form helper compiled before extending the proof.
An unavailable compile server was retried; this did not change the sandbox or item.

The resumed attempt repaired a basis-extension rewrite in
`lattice_inclusion_length`: rewrite the coerced R-basis vector using
`Basis.extendOfIsLattice_apply` before applying `Basis.equiv_apply`.

The current resumption removed the added `open Module` command and qualified
`Module.Basis` references, preserving the original importer-visible commands.
The subsequent dry run passed. A standalone compile request received no server
answer within 204 seconds; the successful delivery dry run independently compiled
the same source.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
