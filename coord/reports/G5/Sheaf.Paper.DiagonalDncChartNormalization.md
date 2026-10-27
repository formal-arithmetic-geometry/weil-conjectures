## What changed

Prove `WeilConjectures.PurityFiniteSetting.chartAffineGamma_zero` without changing
its signature. Cancel the coefficient-source maps using the proved
`vectorIntegration_identity_unit`, use the literal identity affine counit, and
identify the compact-support comparison with `compact_comparison_zero`.
The helper identifies the two coefficient-ring presentations once, inside its proof,
by reducing the positive level to a successor. Its public statement uses the actual
finite coefficient ring; the item calls it without expensive definitional conversion.

The new, fully proved module `Sheaf.Paper.VectorIntegrationIdentityAdjunct` proves
`AlgebraicGeometry.ProEtale.VectorIntegrationChart.identityAdjunct`: the ordinary
adjunct of the compact-support identity comparison is the inverse canonical
exceptional-identity comparison at the coefficient unit. It applies the existing
`affineTranspose_unit_coordinates` at zero. The ordered source and integration
transpose are identities by their HEq specifications. Comparison detects equality
because its adjunction unit at the target is invertible: the target is isomorphic
to the bounded-below coefficient unit, using `sk-prop-sf-comparison`.

Factor the existing coordinate-neighbourhood proof
`chartCoordinateDifferences_neighbourhood`: its etaleness calculation is now a
proved private helper, so the subsequent cone equations no longer retain the large
raw-map and translation construction in their context. The argument and signature
are unchanged.

Normalize the trace in proved private helpers before applying the large adjunction
and comparison functors. Scoped reducibility attributes prevent unfolding those
functors. Also keep the source and normal coordinate comparisons locally irreducible
at the final statement. The identity-adjunction calculation lives in its own
module, and its coefficient-ring presentation is normalized within its proof,
to keep each file within the compile-time limit. No existing
public declaration signature, data construction, attribute or downstream module changes.
The geometry declarations are re-exported at their original names by the item.
The identity-adjunction imports of the item are proof-only. The extracted geometry
module is publicly imported to preserve its existing declarations for all callers.
The identity helper module publicly imports
only the modules supplying its statement; the integration-coordinate theory is a
private proof dependency. Update its node's proof, proof_deps and
proof_origin and the geometry Lean attachments, and add both proved component nodes. Empty schemes require no
exception in either argument. No tool_uses approvals are edited.

Validation: `lcompile.py --all` passed for all three final files, without warnings
or diagnostic options. The service accepted every file under its 60-second limit.
The geometry extraction follows the scoped reducibility and proof-context improvements
and the delivery's refusal of the earlier 61-second large file.

## Proved and sorry left

Closed one of the item's eight initial holes:
`WeilConjectures.PurityFiniteSetting.chartAffineGamma_zero`.
Added holes: zero. Split-off sorry statements: zero.
The new `AlgebraicGeometry.ProEtale.VectorIntegrationChart.identityAdjunct` is proved.
Its proof uses the existing stated
`AlgebraicGeometry.ProEtale.VectorIntegrationChart.affineTranspose_unit_coordinates`;
that declaration's pre-existing sorry remains in its own module.

Seven holes remain in this item, all attached to
`lem-pur-diagonal-dnc-chart-normalization`:

- `WeilConjectures.PurityFiniteSetting.diagonal_dnc_chart_normalization`
- `WeilConjectures.PurityFiniteSetting.chartOrientation_etale_restriction`
- `WeilConjectures.PurityFiniteSetting.chartOrientation_open_baseChange`
- `WeilConjectures.PurityFiniteSetting.chartGamma_eq_inverseOrientation`
- `WeilConjectures.PurityFiniteSetting.chartNormal_vectorPurity_normalization`
- `WeilConjectures.PurityFiniteSetting.chartEpsilon_standing_composition`
- `WeilConjectures.PurityFiniteSetting.chartDiagonalDelta_coordinate_identity`

## No longer needed

None. No original imports, nodes, modules, or unit steps are withdrawn. The planned
normalization dependencies are retained for the seven original obligations.

## Where the brief, the DAG or earlier work was wrong

The planned dependency `Sheaf.Paper.ChartExceptionalMateCoherence` already reaches
this item through its imports, so it cannot be imported here without a cycle.
The import-direction checker confirmed that issue. The rank-zero proof instead uses
the acyclic `VectorIntegrationUnitTranspose` through the new proved helper.
The other normalization obligations have not been changed.

## New nodes

`lem-pur-vector-integration-identity-adjunct`, implemented by the fully proved
`AlgebraicGeometry.ProEtale.VectorIntegrationChart.identityAdjunct` in
`Sheaf.Paper.VectorIntegrationIdentityAdjunct`. This isolates the ordinary identity
adjunct; coefficient descent and affine-counit normalization in the item remain
separate parts of its proof. It introduces no sorry.

`lem-pur-chart-coordinate-difference-neighbourhood`, implemented in
`Sheaf.Paper.ChartCoordinateDifferenceNeighbourhood`. It relocates the already proved
`chartCoordinateDifferences_neighbourhood` and its unchanged coordinate-map definition,
with both original names publicly re-exported by the item. It introduces no sorry.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
