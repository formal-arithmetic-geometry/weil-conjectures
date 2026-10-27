## What changed

Replaced the body of `koszul_finite_augmentation` by an explicit construction from
scalar cones. For each n, descend from the cone using zero on its shifted coordinate
and the actual quotient unit after the tensor right unitor on its other coordinate.
The cone equations prove the unit identity. The degreewise formula for this descent
and the normalized second projections prove off-Koszul-degree-zero vanishing and
successor compatibility. The original theorem signature and its public imports stay
unchanged; its new import is private.

Added two modules separating the independent parts of the source argument:
`Sheaf.CategoryTheory.RingedSingletonKoszulCone` contains the genuine tensor-scalar
power construction and the finite linear algebra comparison;
`Sheaf.SixFunctors.ProEtale.InternalQuotientScalarAnnihilation` states the arithmetic
annihilation identity for the prescribed, actual quotient units. Neither statement
asserts the augmentation maps of the item. The former has no residue or quotient;
the latter has no Koszul-to-quotient maps or compatibility assertion.

The two modules involving the actual quotient use the same local irreducibility attributes for
`IntegralConstantModel.pointComparison` and `upperStarFromPoint` as the existing
quotient-tower module, to avoid elaborating their large constructions unnecessarily.
No existing definition, declaration signature, source-library body, or target changed.

## Proved and sorry left

Closed the item's one body hole:
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.koszul_finite_augmentation`
(node `lem-sfb-internal-koszul-finite-augmentation`). The map construction and all
three required equations are Lean proofs from the two independent statements below.
This is a decomposition, not a proof of the entire mathematical obligation.

Added exactly two holes, each the entire proof of a named public theorem in its own
new module:

- `CategoryTheory.ringedSingletonKoszulCone`, node
  `lem-sfb-ringed-singleton-koszul-cone`.
- `AlgebraicGeometry.ProEtale.InternalCompletionTransport.quotient_scalar_annihilation`,
  node `lem-sfb-internal-quotient-scalar-annihilation`.

No sorry remains in the item module. No sorry occurs in a definition or private helper.
`CategoryTheory.ringedSingletonKoszulPower` is an explicit, irreducible construction
from the tensor functor and the single-complex scalar power, with no chosen witness.
Net holes in this packet: one closed, two added. No other modules are edited.

## No longer needed

None pruned. No original public imports were removed. The original arithmetic
coefficient dependencies are now the proof dependencies of the annihilation lemma;
they remain needed. The actual quotient tower and the signed Koszul tensor remain
needed. The finite cone comparison requires only finite free Koszul linear algebra
and the existing tensor-cone API; no K-flat resolution, acyclicity, or derived
inverse-limit comparison is imported for the construction.

Searches found `principalKoszul_dual_tower_comparison`, which provides a normalized
unit comparison but no off-Koszul-degree projection assertion for an arbitrary P.
Specializing it to O[0] and then tensoring is a possible route for the new finite
linear algebra item. The node records the existing negative-duality and tensor-cone
route, rather than treating the discovered comparison as the desired stronger result.

## Where the brief, the DAG or earlier work was wrong

No false statement or target discrepancy found. The old plan's instruction to tensor
the coefficient augmentation hides both the actual transported scalar-annihilation
identity and the normalized finite dual-Koszul presentation. They are now separately
stated with their full source proofs. The construction follows the existing unit
route and makes no flatness or regularity assumption. The new statements were checked
on a=0, invertible a for the general cone assertion, P=0, the zero ring, and empty
sites or schemes. The annihilation assertion uses positive exponent n+1, including
n=0, and does not claim a vanishes in every higher quotient.

## New nodes

`lem-sfb-ringed-singleton-koszul-cone` records the scalar-cone coordinates, normalized
unit, off-degree-zero second projection and successor projection identities. Its
source is the singleton finite free Koszul argument in Stacks 0A0E. Its Lean module
also contains the explicit scalar-power definition needed in its statement.

`lem-sfb-internal-quotient-scalar-annihilation` records the residue-kernel power
calculation and its balancing through the prescribed quotient units and exact
transport. Its sources are Stacks 0A0E and 099M and the original node's coefficient
comparison dependencies. The two new nodes are strictly parts of the original proof;
the combination of their assertions into the augmentation is in the item module.

The original node's proof, proof dependencies and proof origin were updated to match
the cone descent proof. No change records are needed: existing statements and
existing definitions did not change.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
