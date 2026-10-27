## What changed

Proved `AlgebraicGeometry.scheme_unramified_etale_locality` without changing its
statement, public imports, definitions, or attributes. Two proved private helpers
implement the local-ring differential argument and its application to the actual
stalk tower. Composition and arbitrary base change use Mathlib permanence instances;
identity charts prove the forward implication. The converse uses the existing
`scheme_etale_source_target_properties` theorem only for local finite type, and
proves the formal-unramified part using Jacobi-Zariski exactness, formal smoothness,
faithful flatness, and the all-stalks criterion. The DAG proof and dependency list
now describe these direct calls. No other existing module is changed.

The proof covers empty sources by the pointwise criteria, never choosing a point
without receiving one. No surjectivity, quasi-compactness, separation, Noetherian,
or finite-presentation hypothesis was added. For the ring helper, faithful flatness
is needed to detect the zero differential module; formal smoothness is needed for
the injection. Thus neither is silently omitted, including in positive characteristic.

Validation: the final module compiled through `lcompile.py` with exit code 0,
no warnings or errors, in 4.8 seconds. Static checks confirm the original public
theorem signature and public imports are identical, and all Lean lines fit
within 100 columns.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.scheme_unramified_etale_locality`
(node `lem-sfb-scheme-unramified-etale-locality`).
Added 0 holes and split off 0 statements. No `sorry` remains in the item or its
private helpers. The already declared theorem
`AlgebraicGeometry.scheme_etale_source_target_properties` remains an existing
proof dependency with its own `sorry`; it is not changed or newly introduced here.
This is a proof from the declared dependencies, not a claim that the entire
transitive axiom closure is now sorry-free.

## No longer needed

Removed private imports:
- `WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen`
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`
- `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`
- `Mathlib.RingTheory.Unramified.Basic`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `Mathlib.LinearAlgebra.TensorProduct.Defs`
- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`

`WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen` and node
`lem-weil-pbc-unramified-base-change-open` are not used by this proof: direct
Mathlib local-finite-type and formal-unramified base-change instances, followed
by the diagonal criterion, supply the required clause. The restriction clause of
the upstream theorem is unnecessary here; that theorem and its file are preserved.

`Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres` and node
`lem-weil-pbc-etale-smooth-zero-dimensional-fibres` are not used: the Mathlib
Etale-to-Smooth instance supplies smoothness, and no fibre dimension conclusion
is needed. Both obsolete entries were removed from this node's top-level
`tool_uses`; historical review and split-report fields are preserved.

The other removed imports were redundant through the preserved statement imports
and the three retained proof imports. The proof uses the faithful-flat tensor
injection in Mathlib's existing factor order, so the originally planned extra
tensor-factor interchange is unnecessary. No unit statement or unit step is
bypassed, and no module is withdrawn. No other declared proof dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The six-step stalk proof was implementable
from the stated declarations. The stronger fibre-dimension theorem and the
restriction-of-unramified-morphisms theorem were unnecessary as proof imports;
the required parts already have Mathlib instances. The general locality theorem
has a second universe parameter for its family clause; it is explicitly instantiated
to `u` here even though only its pointwise clause is used.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
