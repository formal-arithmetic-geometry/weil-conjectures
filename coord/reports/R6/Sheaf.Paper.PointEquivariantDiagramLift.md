## What changed

Reduced `WeilConjectures.zl_point_equivariant_diagram_lift` to three independent
steps of its original proof: the original-field construction, finite scalar
extension of a supplied realization, and original-stage common-stage inclusion.
The assembly proof is complete: it uses isomorphism extensionality and inversion
to derive the inverse Weil-map formula, cancels the fibre and transport
isomorphisms to prove the local Frobenius equation, and applies both extension
steps to the same original-field diagram. The theorem signature is unchanged.

Extracted the 17 existing definitions verbatim to the publicly reexported
`Sheaf.Paper.PointEquivariantDiagramData`, so the three new step modules can
use their predicates without an import cycle. The new modules are
`Sheaf.Paper.PointEquivariantOriginalDiagram`,
`Sheaf.Paper.PointEquivariantFiniteScalar` and
`Sheaf.Paper.PointEquivariantCommonStage`. The assembly imports them privately.
There are no changes under `lean/WeilConjectures` and no target changes.

The declaration parser confirms the existing theorem and all moved data
signatures are identical. The dependency/user search finds zero current Lean
importers of the original module; the original import path reexports its entire
public interface. The change record is
`coord/changes/R6-point-equivariant-diagram-data.md`.

## Proved and sorry left

Closed the original direct hole in
`WeilConjectures.zl_point_equivariant_diagram_lift`
(node `lem-zl-point-equivariant-diagram-lift`). Its assembly proof derives both
inverse and local Frobenius identities by real Lean isomorphism calculus.
The item module now has zero direct holes.

Added three direct holes, each the whole proof of its public theorem:

- `WeilConjectures.zl_point_equivariant_original_diagram`
  (`lem-zl-point-equivariant-original-diagram`): the original-field diagram,
  exactness and forward Weil-map formula, with literal prescribed data.
- `WeilConjectures.zl_point_equivariant_finite_scalar`
  (`lem-zl-point-equivariant-finite-scalar`): finite scalar extension of any
  supplied realization, with all normalized comparison squares.
- `WeilConjectures.zl_point_equivariant_common_stage`
  (`lem-zl-point-equivariant-common-stage`): literal original-stage inclusion of
  a supplied realization, including exactness and normalized transport.

This is a decomposition, not a net proof: one old hole closed, three added,
net minus two. No definition contains a hole, and no arbitrary data is chosen
from an unproved existence theorem. The extracted data module has zero holes.

Edge cases checked in the statements and written arguments: zero modules and
zero arrows; a terminal index category; arrows incident with the prescribed
object; parallel arrows whose fibres coincide; arbitrary nonsemisimple invertible
operators. The scalar steps assume an existing point realization and impose no
extra naturality or finite-dimensional hypothesis. Naturality and finiteness
are already forced by that realization and the exact point-heart equivalence.
The original-field step retains the original hV, hA and hStar hypotheses.

## No longer needed

No mathematical dependency is pruned. The three old private imports
`Sheaf.Paper.ConstructibleTruncations`,
`Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` and
`Sheaf.SixFunctors.FrobeniusPointTransportNatural` are removed from the assembly
module; they remain dependencies of the split steps in the DAG. The existing
approvals for these generic tools are retained. The private import of
`Mathlib.Algebra.Category.ModuleCat.Descent` stays with the extracted definitions.
All original public imports remain publicly reexported. No module is withdrawn.

The parent node now names exactly the three step nodes used by its Lean proof;
its old proof dependencies remain on those steps where they are needed.

## Where the brief, the DAG or earlier work was wrong

No false statement or source discrepancy found. The original DAG did not expose
the interface glue between original-field lifting and the two coefficient
extension clauses. They are now separate strictly smaller statements: neither
extension theorem constructs an original-field diagram, and the original-field
theorem makes no coefficient-extension claim and omits the inverse and Frobenius
formulas actually proved by the assembly.

The available point-heart theorem states its finite equivalence on F.val,
whereas this item's input is the canonical Shrink coefficient model of F.
The original-field step's docstring and node explicitly record the necessary
transport across the Shrink algebra equivalence and its scalar/fibre comparison.
This is required glue, not an additional mathematical assumption.

## New nodes

`def-zl-point-equivariant-diagram-realization` owns the 17 unchanged data
constructions extracted to `PointEquivariantDiagramData`. It has no holes.

`lem-zl-point-equivariant-original-diagram` is steps 1--5 of the original
argument, including the Shrink comparison and forward Weil-map formula.
It is strictly smaller than the full theorem and excludes coefficient extensions.

`lem-zl-point-equivariant-finite-scalar` is step 7, for an arbitrary supplied
realization and any finite coefficient embedding. It is independent of the
original-field construction and literal-prescribed-object choice.

`lem-zl-point-equivariant-common-stage` is step 8, for a supplied realization
at its original coefficient stage, with no coefficient enlargement.

All new nodes have self-contained statements, source-linked proof steps,
three kinds of Mathlib searches, and exact Lean records. The unit route remains
unchanged. Change record: `coord/changes/R6-point-equivariant-diagram-data.md`.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
