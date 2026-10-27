## What changed

Replaced `AlgebraicGeometry.ProEtale.VectorIntegrationChart.vectorIntegration_chart_comparison`
by a complete assembly proof from three strictly smaller intermediate statements and the
existing `AffineOrderedIntegration.ordered_integration_transposes` theorem.

Extracted the sixteen existing coordinate/helper declarations, including their four proved
lemmas, into `Sheaf.Paper.VectorIntegrationChartCoordinates`. Names, types, bodies and
visibility are unchanged; the item publicly reexports this module, including every original
public prerequisite. This structural extraction prevents a cycle when the intermediate
statements refer to the actual maps. It does not address a compile timeout. The extracted
module compiled on its first submission.

`VectorIntegrationUnitTranspose` constructs the ordinary ordered affine trace and its
comparison-image adjoint without using bundle restriction or purity. Its endpoint transport
`affineTranspose_existsUnique` is proved by induction on the tower/projection dependent pair
and equality elimination. It leaves only the coefficient-unit site-transpose calculation.
`VectorIntegrationChartTranspose` isolates restriction of the global integration adjunct to
that ordinary affine adjunct, before any ordered-purity identification.
`AffineIntegrationExponentTransition` isolates root-transition naturality for the ordinary
affine adjunct, with no vector bundle or frame. The item privately imports the chart and exponent modules, which reexport the shared
unit-transpose prerequisite for its proof. Each deferred statement has a source, full proof in words and its own DAG node.

Updated the item's proof route and declaration list, and added nodes owning the extracted
coordinate interface and all three intermediate modules. Change record:
`coord/changes/A3-vector-chart-coordinates-extraction.md`.

## Proved and sorry left

Closed the body of
`AlgebraicGeometry.ProEtale.VectorIntegrationChart.vectorIntegration_chart_comparison`
(node `lem-pur-vector-integration-chart-comparison`), the only original hole.
This is a **decomposition**, not a completed proof of its transitive dependencies: one
original hole is replaced by three lower holes, so the immediate net is minus two.

New proved helper:
`AlgebraicGeometry.ProEtale.VectorIntegrationChart.affineTranspose_existsUnique`.
The four previously proved helpers `unit_properties`, `open_geometry`,
`orderedSourceIso_existsUnique` and `restrictedMap_existsUnique` are preserved verbatim.
No holes remain in the item or the extracted coordinate module.

Every new hole, with namespace `AlgebraicGeometry.ProEtale.VectorIntegrationChart`:

- `chartTranspose_eq_affine`: `lem-pur-vector-chart-restricted-affine-transpose`;
- `affineTranspose_unit_coordinates`: `lem-pur-affine-unit-transpose-coordinates`;
- `affineTranspose_exponent_transition`: `lem-pur-affine-transpose-exponent-transition`.

No definition contains a hole. The affine transpose is a real ordinary counit adjunct;
its only choice transports a specified morphism uniquely by HEq.

## No longer needed

No module is withdrawn. No upstream declaration or proof is changed. The four original
public imports and three original private imports move with the coordinate code, so none
is falsely counted as pruned. The item's direct imports are replaced by the public
coordinate interface and two private intermediate modules. The redundant direct import
of VectorIntegrationUnitTranspose was removed: both intermediate modules already
publicly import it. The old geometric and
coefficient-unit inputs remain needed by the extracted helper proofs. Ordinary bundle
normalization, base-change mate naturality, site normalization and exponent transport
remain needed by the new intermediate arguments, rather than being bypassed.

The old dependencies `cor-pur-vector-bundle-purity` and
`def-pur-vector-purity-normalization` are unnecessary as separate proof steps for this
specific Lean statement: `restrictedRaw` already *defines* the left map as the actual
ordinary integration adjunct. Its identification with inverse vector purity is part of
that API's interpretation, not an additional equality needed in this proof. Their modules
remain publicly reexported because this packet preserves the interface. No claim of a
pruned module or transitive hole is made.

## Where the brief, the DAG or earlier work was wrong

No false mathematical statement or target change was found. The listed proof dependencies
do not directly state the coefficient-coordinate coherence calculations needed to connect
this module's `restrictedRaw` and `orderedMap`: they supply normalized traces and transposes
in different explicit coordinates. The three new statements isolate those calculations
rather than restating `ChartComparison`. The old Lean attachment listed sixteen helper
names as if they must stay in the theorem module; the coordinate extraction preserves them
under the identical public names and records their new owning module.

Edge cases checked in the argument: dimension zero uses identity adjunctions and identity
root transition, not the positive-dimensional comparison-unit formula; empty opens and
bases are allowed throughout; every modulus is a positive annihilating ell-power, including
level one and ramified levels. No nonempty-base, primitive-root, coefficient-field,
ramification-divisibility or Kummer-flatness hypothesis is introduced. The unit's route is
kept: ordinary affine counit, exceptional transpose, then ordered affine comparison.

## New nodes

`def-pur-vector-chart-comparison-coordinates`: the exact preexisting canonical coordinate
interface, relocated without mathematical change. Its existing four proofs remain closed.

`lem-pur-affine-unit-transpose-coordinates`: ordinary affine-counit adjunct in bounded site
transpose coordinates at the coefficient unit. Its new coordinate transport lemma is proved;
its unit projection/site comparison calculation is deferred. Unlike the original item it
has no bundle, frame, restricted global integration or exponent-independence conclusion.

`lem-pur-vector-chart-restricted-affine-transpose`: restrict the global adjunct to the
ordinary affine adjunct. It uses no ordered purity comparison and asserts no exponent
independence; it is exactly the local-adjunction step of the source proof.

`lem-pur-affine-transpose-exponent-transition`: source naturality of the affine adjunct
under the prescribed root transition. It involves no vector bundle, chart or ordered
purity map. The existing exponent theorem supplies the ordered trace transition.

Validation: all five delivered modules compiled together through `lcompile.py --all`.
The subsequent delivery preflight recompiles the final instance-style and redundant-import
cleanup and runs the declaration/axiom probes.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
