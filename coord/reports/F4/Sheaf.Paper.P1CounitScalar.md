## What changed

Partial delivery. Added proved private helpers in `Sheaf.Paper.P1CounitScalar`:
`transpose_of_counit_square`, `tensor_trace_counit_square`,
`coefficient_line_sheaf_eq`, `comparison_balancing_sheaf`,
`transported_right_unit`, `transported_right_unit_named`. These formalize the projection cancellation, generator
comparison, unit transport, and adjunction transpose needed by the planned proof.
The public theorem statement and its original proof hole are unchanged. Its
visibility follows the existing public section, as in the current library. The returned
packet used an explicit `public theorem` beneath a scoped attribute command; the
landing declaration scanner did not recognize that modifier and reported the
existing name as removed. The repair restores the normal `theorem` command,
removes that command wrapper, and uses the original signature instance budget
of 4096. The declaration name and statement remain unchanged.

## Proved and sorry left

Closed 0 of the item's 1 holes; added 0 holes; split off 0 statements.
The one remaining hole is `AlgebraicGeometry.Etale.p1_counit_scalar`, node
`lem-sp-p1-counit-scalar`. All six private helpers listed above are proved.
No definitions are changed.

A complete attempted counit assembly repeatedly exceeded the 60-second check.
The packet retains the verified parts and the original named theorem hole rather
than claiming the attempted assembly is a completed proof. It is not a no-op:
the argument's generator and categorical parts have been formalized.

## No longer needed

No DAG dependency or module is pruned: the public counit theorem remains unfinished,
so its original planned dependencies remain needed. No module is withdrawn.
The delivered helpers use VectorTraceScalarDescent and its existing finite Tate
source normalization; no new statement dependency is invented.

## Where the brief, the DAG or earlier work was wrong

The original plan is retained. The difficult implementation issue is the size of
concrete derived monoidal instance comparisons: the separately checked abstract
calculations and balancing proof do not suffice to make the full assembled term
pass its kernel check within 60 seconds. No target signature or mathematical
normalization was weakened. This report claims only the actual partial work.

The returned landing failure was a declaration-indexing mismatch: the tool did
not recognize `public theorem`. This repair uses the library's standard public-section
syntax. The duplicate cached sheafification statement was advisory only; it is a
private instance cache, matching the existing local cache pattern.

Validation of the repair: the item compiles, and a separately compiled module
with an ordinary `import Sheaf.Paper.P1CounitScalar` successfully checks
`AlgebraicGeometry.Etale.p1_counit_scalar`. The theorem signature is byte-identical
to current main. No consumer adaptation or alias is needed.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
