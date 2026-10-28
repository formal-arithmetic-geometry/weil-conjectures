# AlgebraicGeometry.Scheme.constantAdicQuotientRealization_iso_lift

## Reason

The original proof plan combined two independent facts: lifting a realized
isomorphism to a coefficient morphism, and reflecting isomorphisms of a
realized coefficient morphism.  The available library declarations do not
provide either specialized fact as a single theorem.  The target statement and
all its binders remain unchanged; the proof is decomposed into two strictly
smaller public statements.

## Changed DAG route

The item node now depends on:

- `lem-weil-pbc-constant-adic-quotient-realization-iso-hom-lift`, and
- `lem-weil-pbc-constant-adic-quotient-realization-reflects-iso-of-map`.

The first split statement supplies a coefficient morphism whose realization is
the given isomorphism.  The second supplies `IsIso` for a coefficient morphism
from `IsIso` of its realization.  Their composition is the unchanged target
conclusion.

## Interface impact

Two new Sheaf modules and their declarations are added.  No existing source
library declaration is changed, and the target theorem signature is unchanged.
The item module gains proof-only imports of the two new modules.
