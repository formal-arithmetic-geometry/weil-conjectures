## What changed

Proved `AlgebraicGeometry.Scheme.exists_lisse_open_dimension_drop` in
`Sheaf.AlgebraicGeometry.LisseOpenDimensionDrop`, preserving its complete signature.
Use the given stratification and `finite_locally_constant_module_values_iff` to
supply the source library's constructibility class. Generic constancy supplies the
same dense lisse open in all cases. For a nonempty scheme, finite type supplies
local Noetherianity and finite dimension; the closure of a point excludes dimension
bottom. The existing nowhere-dense dimension-drop theorem gives the strict
inequality. For an empty scheme, pointwise extensionality proves this open is top.

Updated the existing node's proof, proof dependencies and proof origin to match
this proof. No statement, definition, public interface or other module changed.
The original public imports remain to preserve their exported interface.

Validation: lcompile.py compiled the delivered module cleanly in 2.5 seconds.
The source blueprint statement, existing node, dependency signatures and unit
realization record were read; the unit's route is preserved.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.exists_lisse_open_dimension_drop`
(node `fin2-lem-lisse-dense-open`).

No sorry remains in the item. No holes were added or split off. No new theorem,
definition, axiom or intermediate module was introduced. The proof uses the
existing declared dependencies as required by stage 3; their transitive axioms
are reported by the delivery probe.

## No longer needed

Removed these redundant proof imports:

- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`: the hypothesis already
  carries precisely the source library's `Stratification`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`: no separate partition
  record or conversion is needed.
- `WeilConjectures.Topology.Stratification`: supplied by the constructibility API;
  no direct use beyond the existing witness.
- `WeilConjectures.AlgebraicGeometry.IsFiniteTypeEtaleModuleSheaf`: the finite-value
  equivalence is used directly, without a finite-type-sheaf argument here.
- `Mathlib.AlgebraicGeometry.Noetherian`: supplied by the dimension-drop import.
- `WeilConjectures.ConstructibleSheaf.Defs`: supplied by the existing public
  constructibility import and generic constancy.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: supplied by the dimension and
  dimension-drop modules; no local-dimension theorem is used.

Removed the duplicate private import of
`WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues`.
Removed `def-constructible-stratification` and `def-kun-dimension` from the item's
proof dependencies: the first would introduce an unused wrapper interface; the
second's local-dimension notion is unused and its global notion is already the
`topologicalKrullDim` used throughout. All five existing tool lemmas remain used.
These are removals from this proof, not assertions that other importers can prune
the same modules.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The plan's explicit partition transfer
is unnecessary because both constructibility predicates already use the same
`Scheme.Stratification`. Generic constancy works on the empty scheme as well,
so a separate empty-cover construction can be omitted. Its open must equal top
on an empty space. Nonemptiness of the space does not synthesize nonemptiness of
`IrreducibleCloseds` automatically: the Lean proof explicitly constructs the
closure of a point.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
