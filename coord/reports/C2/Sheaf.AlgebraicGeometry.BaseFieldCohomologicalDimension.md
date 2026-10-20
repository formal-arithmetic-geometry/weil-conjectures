## What changed

The algebraically closed clause of `AlgebraicGeometry.ProEtale.cohomologicalDimension_baseField`
is proved. It uses the separably closed torsion bound and the étale/pro-étale comparison at the
identity morphism of `Spec K`. The finite-field clause is reduced by the same comparison to the
new prerequisite theorem `AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_one_of_finite_baseField`.
The item module imports only the declarations used by this proof. A new module states that
finite-field torsion prerequisite.

## Proved and sorry left

Closed the item theorem `cohomologicalDimension_baseField` (one original sorry). The new
prerequisite theorem `hasTorsionEtaleCohomologicalDimensionLE_one_of_finite_baseField` remains
`sorry` and is recorded by node `det-base-field-cd-finite-torsion-bound`; it contains the
independent finite-field absolute-Galois/cochain argument described in its docstring.

## No longer needed

The proof does not use the original imports for the sheaf/Galois equivalence, field sections,
continuous cochain construction, finite-field absolute Galois group, cyclic inflation, or the
étale derived lower-shriek API. Those proof-only imports were removed from the item module.
The corresponding DAG dependencies remain available for the split finite-field prerequisite.

## Where the brief, the DAG or earlier work was wrong

The existing node `lem-sfb-finite-field-all-torsion-cd` records the finite-field torsion bound,
but its Lean module imports this item and invokes the item theorem in its own proof. Importing
that module here would create an import cycle. The new node isolates the same prerequisite with
a module that does not import this item; its docstring records the cycle and the direct
absolute-Galois proof still required.

## New nodes

`det-base-field-cd-finite-torsion-bound` records the finite-field torsion bound used by the
finite clause and is implemented by
`Sheaf.AlgebraicGeometry.BaseFieldFiniteTorsionCohomologicalDimension`.

Change record: `coord/changes/base-field-cd-open-category-theory.md` records the proof-only
namespace opening required for identity-morphism notation.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
