## What changed

Filled `FiniteLevelComparison.scalarMap_existsUnique` using the monoidal constant-sheaf
comparison and the sheafification adjunction. A private sectionwise construction turns its
monoid map into a commutative-ring map. The adjunction proves both its normalization and
uniqueness.

Filled `FiniteLevelComparison.encoding_properties`: forgetting the normalized scalar map to
abelian sheaves identifies it with `constantSchemeIso`, so it is invertible. Compose the
section-action equivalence, the two scalar-restriction equivalences and the existing
constant-ring module equivalence. The composite retains the underlying additive maps, so
additivity holds sectionwise.
The existing signatures, canonical definitions and coefficient normalizations are preserved.
The item node records this direct scalar-universe construction and its two generic equivalence
dependencies; the remaining internal comparison steps are retained.

## Proved and sorry left

Closed two of the original nine holes, both belonging to
`lem-sp-finite-level-projection-factors`:

- `AlgebraicGeometry.ProEtale.FiniteLevelComparison.scalarMap_existsUnique`.
- `AlgebraicGeometry.ProEtale.FiniteLevelComparison.encoding_properties`.

No holes added or split off. Seven original named theorem holes remain, all attached to
`lem-sp-finite-level-projection-factors`:

- `AlgebraicGeometry.ProEtale.FiniteLevelComparison.monoidal_existsUnique`.
- `AlgebraicGeometry.ProEtale.FiniteLevelComparison.pushMap_existsUnique`.
- `AlgebraicGeometry.ProEtale.FiniteLevelComparison.proper_adjunction_comparison`.
- `AlgebraicGeometry.ProEtale.FiniteLevelComparison.open_adjunction_comparison`.
- `AlgebraicGeometry.ProEtale.FiniteLevelComparison.proper_projection_comparison`.
- `AlgebraicGeometry.ProEtale.FiniteLevelComparison.open_projection_comparison`.
- `AlgebraicGeometry.ProEtale.FiniteLevelComparison.coefficient_models`.

The previously proved `finite_level_projection_factors` and other existing proofs are retained.
Compilation and the delivery probe are the validation gates.

## No longer needed

None. No new proof-dependency import is needed for these two proofs. All original public
imports are retained as the existing module interface; the private imports still supply the
proved ordinary finite-level assertion. No node or module is withdrawn and the unit route is
preserved.

## Where the brief, the DAG or earlier work was wrong

The ordinary projection-factor theorem was already proved by the preceding delivery; this
item's actual nine holes belong to its retained internal-coefficient comparison clauses.
The declared finite-discrete equivalence uses `A : Type u` and fixed scalars `ULift A`, while
this item fixes `A : Type (u + 1)` with no lift. The proofs therefore use the existing generic
section-action and constant-ring equivalences at the actual scalar universe. No statement
change is needed. Empty schemes and the zero ring require no additional hypothesis: the
sheafification Hom bijection and the scalar-restriction inverse identities apply unchanged.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
