## What changed

Proved `WeilConjectures.scalar_cochain_averaging_primitives` from the existing
finite-quotient averaging declaration and a new, proved algebraic helper
`WeilConjectures.invariant_average_cochain_identity`. No existing signature,
attribute, visibility, or definition body changed.

The finite primitive is the actual signed finite sum on the same quotient,
pulled back to the original group. Its slices lie in the existing averaging
submodule. The finite average's specified formula, normalization, invariance
and contraction identify and bound that primitive. No completeness is used.

The complete primitive is constructed by continuously currying the last
variable, composing with the supplied continuous linear functional, and
multiplying by the sign. Pointwise linearity gives scalar linearity and
parameter naturality; the supremum norm bounds give contraction. Both primitive
identities use the same algebraic calculation, including degree one and empty
parameter spaces. The construction chooses no data from a holed existence
statement: `bbar`, `b` and `H` are explicit maps, and the submodule average is
used only to prove their properties.

Added private continuous-map wrappers in the item and private tuple identities
in the new helper. Updated the item's proof steps and dependencies. Replaced
the unused complete-integral public import by the four Mathlib imports its
statements require. The change record is
`coord/changes/scalar-cochain-complete-integral-import.md`.

Remote single-file validation passed without warnings: the algebraic helper in
2.7 seconds, the item in 8.8 seconds, and its sole direct importer
`Sheaf.CategoryTheory.PrimeToEllFiniteQuotientSheafAugmentation` in 26.1 seconds.
The importer was compiled unchanged against the delivered modules and its
temporary sandbox copy was removed.

## Proved and sorry left

Closed the item's one hole:
`WeilConjectures.scalar_cochain_averaging_primitives`.
Added zero holes. The helper
`WeilConjectures.invariant_average_cochain_identity` is proved without `sorry`.
There are no remaining `sorry` declarations in the delivery.

The existing dependency
`ContinuousMap.exists_finiteQuotientContractiveAverage`
(node `lem-sfb-finite-quotient-contractive-average`) remains a holed theorem;
its module is not changed by this delivery.

## No longer needed

Removed the import and proof dependency
`Sheaf.Analysis.PrimeToEllCompleteScalarIntegral`,
node `lem-sfb-prime-to-ell-complete-scalar-integral`.
The complete conclusion already quantifies over a supplied normalized invariant
continuous linear functional. Mathlib currying and composition construct its
continuous parameter family directly, for the actual supplied functional.
There is no need to prove total disconnectedness, bundle products as Profinite,
or choose an integral from the existence theorem and compare it to the given one.
The finite average dependency remains necessary.

No declarations or modules are withdrawn. The existing statement dependency
on the complete-integral node is retained because the node's prose refers to
that normalized integral; the proof itself uses no declaration from it.

## Where the brief, the DAG or earlier work was wrong

The old complete proof plan invoked the parameter clause of an existential
integral theorem to construct maps for an arbitrary integral supplied by the
item. That clause concerns the theorem's chosen integral; using it for the
supplied one would require an additional uniqueness argument. The direct
continuous currying construction avoids that mismatch and works without
completeness or the finite-quotient compatibility premise in this branch.
Those hypotheses remain unchanged in the original theorem.

The finite-average dependency takes a `NormedAlgebra` rather than an isometric
ring homomorphism. A local instance from `iota.toAlgebra` and its norm isometry
bridges these equivalent input interfaces, without changing a shared definition.

The blueprint paragraph supplies geometric motivation only; its analytic
expansion and exact-reference-WANTED status are preserved. The blueprint
ancestor search returns null for this inherited chain. Whole-blueprint searches
for averaging cocycles and library searches found no existing contraction lemma
with this averaging-domain interface. The unit's route is unchanged.

## New nodes

`lem-sfb-invariant-average-cochain-identity`, realized by
`Sheaf.Analysis.InvariantAverageCochainIdentity`, isolates and proves the purely
algebraic part of the original steps 3 and 4. It is a normalized invariant
functional on any vector space faithfully represented by group functions,
with no topology, norms, finite quotients, or primitive existence claim. Its
proof lifts the appended-variable cocycle equation into the averaging domain,
applies the functional, and cancels the two signs. Small cases checked are
n=0 (the cocycle vanishes), a trivial group (the alternating signs still give
the primitive), and empty parameter types (vacuous). Searches are recorded from
actual msearch results. No additional holes are split off.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
