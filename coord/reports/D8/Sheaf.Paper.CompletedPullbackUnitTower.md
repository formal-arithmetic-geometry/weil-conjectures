## What changed

Proved `AlgebraicGeometry.Scheme.CompletedPullbackUnitTower.inverse_finiteLimits` and
`AlgebraicGeometry.Scheme.CompletedPullbackUnitTower.canonicalInverseImageData_existsUnique`
in `lean/Sheaf/Paper/CompletedPullbackUnitTower.lean`.

Left exactness follows from scheme base change, the AsSmall equivalences, and Mathlib's
small-site inverse-image instance. The algebraic lift is constructed for arbitrary small
sites and specialized to the transported pro-etale sites. Its ring and module comparisons
are precisely the set-adjoints of the actual ring and module adjunction units. Unit
presentations prove invertibility; the adjunction transports every operation graph.
The constant comparison comes from the two constant-sheaf adjunctions and is proved equal
to the specified sheafified constant-section adjunct. The normalized predicate determines
all data fields, and extensionality and proof irrelevance prove uniqueness.

Added only proof imports `Sheaf.CategoryTheory.SheafPullbackForgetComparison` and
`Sheaf.CategoryTheory.ModuleInverseImageAdjunction`, plus proved private construction and
normalization helpers. Cached local Prop-valued adjoint instances reduce repeated typeclass
search. Every existing public signature and definition body is unchanged.

Updated the existing node's proof, proof_deps and proof_origin with the geometric-lift
prerequisite and its two existing dependency nodes. The original tower proof route remains.
No definition repair, consumer adaptation, or new public declaration occurs.
The static command audit requests a record for the private helper section; it is
`coord/changes/completed-pullback-unit-tower-private-context.md`. The consumer audit finds
zero downstream Lean modules and only this module uses the two proved declarations.

Validation: remote single-file compilation succeeds. `#print axioms` for each of the two
proved declarations reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
Both new proof imports pass the import-direction check. The first delivery attempt
pushed nothing: preflight required the above scope/visibility change record for the new
section variables and local instance attribute. This packet supplies that record.

## Proved and sorry left

Closed 2 of the item's original 3 holes:

- `AlgebraicGeometry.Scheme.CompletedPullbackUnitTower.inverse_finiteLimits`.
- `AlgebraicGeometry.Scheme.CompletedPullbackUnitTower.canonicalInverseImageData_existsUnique`.

Added 0 holes and split off 0 statements. One original hole remains, unchanged:

- `AlgebraicGeometry.Scheme.CompletedPullbackUnitTower.completedPullbackUnitTower`,
  node `lem-sf-cbc-completed-pullback-unit-tower`.

The remaining hole concerns the strict derived quotient tower and its normalized finite
projections. This is a delivery of two proved prerequisites in a module with multiple holes,
not a decomposition of the remaining tower theorem.

## No longer needed

None. No imports, nodes, modules, or declarations were withdrawn. The original tower
proof dependencies remain required by the retained theorem and its unchanged proof plan.
The two added imports supply the actual forgetful and module-unit comparisons used here.

## Where the brief, the DAG or earlier work was wrong

The planned use of `AdicCompletionReduction` is not a direct application at the current
interface: that theorem uses the original pro-etale site of a scheme in universe t and
coefficients in Type t, whereas this item uses the transported small site and coefficients
in Type (t + 1). A proof of the remaining tower theorem must transport the coefficient,
localization, strict-limit, unit, and finite-evaluation comparisons, or establish the
corresponding result directly on this small site. This does not dispute the mathematical
statement, and this delivery changes neither interface.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
