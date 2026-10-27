## What changed

Repaired the returned packet at `19b183949de` (reviewer `C-19b18`). The landing
failure came from a reviewer-fix filename: `tools/batch_land.py` maps a change
record to `<stem>.change.md`, while the failed attachment was named
`finite-free-scalar-site-universes.md`. The change record now documents its
accepted attachment name, `finite-free-scalar-site-universes.change.md`. The other
record's accepted attachment name is
`finite-scalar-coordinate-proof-instances.change.md`. Both records remain in this
packet at their original `coord/changes/*.md` destinations, with status `open`.
The mathematical work retained from the returned head is rebased by `deliver3.py`
on the current `sheaf-dag`; comparison with the shared source found the original
five holes still present and neither change record landed. The fresh server compile
passed with no diagnostics (44.0 seconds for the item). The unchanged direct consumer
`CompactSupportStrictScalarMate` also compiled against both rebuilt sandbox modules
in 35.6 seconds; it requires no adaptation.

Filled the five proofs in `Sheaf.Paper.FiniteScalarCoordinateData`, retaining every
existing public mathematical statement and construction. Private helpers generalize the finite-basis
section calculation to the site's separate object and morphism universes, transport it
through the sheafification unit, prove naturality and pure-tensor extensionality, and
localize the resulting natural isomorphism. Whole strict diagrams use the pointwise
product comparison before localization. The node proof and proof dependencies now
record this route. The fresh server compile passed with no diagnostics: the item checked in 44.0 seconds.
Local irreducibility boundaries keep the final tower normalization types from unfolding
the exact-localization construction repeatedly. All helper definitions are explicit constructions, and all private
helper theorems are proved. The public `scalarTowerDerived_products` and `scalarTower_products` instances name
the existing finite-product proofs for reuse in coordinate types. The latter was
added during this repair after the delivery's local check timed out despite the
successful server check. Caching ordinary tower products reduced a clean full-module
check to 36.3 seconds, without changing an existing declaration type or proof formula.

The existing `FiniteFreeScalarExtension` proof helpers are generalized privately to
separate site universes, with the public cochain theorem unchanged. The item imports
these helpers and constructs the normalized natural comparison from them. The helper
implementation uses the explicit tensor presheaf isomorphism and its invertible
sheafification unit; no new public declarations are added to that module. Its node now
records this sheafification-unit proof in place of the general comparison argument.

## Proved and sorry left

Closed the five original holes, all under `WeilConjectures.PurStrictScalar`:

- `ordinaryCoordinates_existsUnique`
- `finiteScalar_exact`
- `derivedCoordinates_existsUnique`
- `ordinaryTowerCoordinates_existsUnique`
- `derivedTowerCoordinates_existsUnique`

No holes remain in the delivered module. No holes are added, and none are split off.
The proofs use the already declared scalar extension and derived counit data from
`BoundedConstructibleTower`, as intended by the stage's dependency boundary.

## No longer needed

No imports or modules are pruned. The existing finite-basis module is retained and
reused after generalizing its private helpers. Every original statement dependency
is retained; there were no original proof dependencies to prune.

## Where the brief, the DAG or earlier work was wrong

The node's proof was empty. It is now populated with the actual finite-basis and
localization argument. No mathematical statement was found false. The calculation
uses arbitrary `Fin d`, including the empty basis: product extensionality and tensor
coordinates do not assume positive rank. The tower definitions retain the exact-localization construction, with shared proposition
instances and explicit result types. The whole-cochain normalization predicate is named
to share its expression when choosing the uniquely normalized coordinates. Coordinate definitions choose from the existence
part of their same uniqueness theorems; both old and new choices obey the same
normalization, so uniqueness identifies them. A named finite-product instance for
the derived tower category prevents repeated expansion of its proof. These compile
performance changes and the finite-basis helper generalization are recorded in
`coord/changes/finite-scalar-coordinate-proof-instances.md` and
`coord/changes/finite-free-scalar-site-universes.md`; no mathematical statement
change or consumer adaptation is needed.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
