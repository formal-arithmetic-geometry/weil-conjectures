## What changed

Proved `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteEtaleSectionIntegration`
with its existing statement and docstring unchanged. Substitute d=0, obtain
etaleness and separatedness of the normal projection by base change from the
rank-zero deformation projection, postcompose with the normal-section coordinate
isomorphism, apply the two factor identities, and cancel zeroLineIso.

Added four proved companion modules:

- `Sheaf.Paper.FiniteEtaleSpecializationCoordinates` transports the existing
  etale sum-adjunction exchange to the actual section maps. It constructs the
  constant comparison explicitly, proves its normalization at one, uses uniqueness
  to identify kappa with that comparison, and evaluates at zero.
- `Sheaf.Paper.FiniteUnitCoordinateIdentifications` identifies the ordinary
  constant pullback component with the monoidal unit map. Its private helpers
  prove the coefficient-category identities before specializing to ModuleCat A.
- `Sheaf.Paper.RankZeroBundleSectionCoordinates` computes the specified
  identity-adjunction comparison for any rank-zero bundle in normalized etale
  section coordinates. It has no integration or deformation hypothesis.
- `Sheaf.Paper.FiniteRankZeroNormalIntegration` identifies the actual integration
  adjoint with the existing normalized bundle orientation, applies its rank-zero
  normalization, and transports section coordinates through the specified
  cone/bundle square.

The two imports added to the existing item are private proof imports. No other
existing Lean module, public import, definition, instance, declaration signature
or target statement is changed. Local instance caching and reducibility attributes
in the new modules do not affect importers. The item's DAG route and the companion
nodes follow the Lean proofs. No change record or forced adaptation is needed.

Single-file compilation succeeded for every proof. The final bundle-coordinate,
integration-factor and item checks took 28.6, 29.2 and 15.8 seconds respectively;
the separate coefficient-unit check passed in 55.6 seconds. The specialization
factor also compiled. Profiling isolated the expensive concrete coefficient-unit
conversion and the bundle-coordinate calculation; the proved calculations have
separate files after local caching and generic coefficient-category lemmas were
tested. Development profiling options and unused simp arguments were removed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteEtaleSectionIntegration`.

Also proved the new companion declarations:

- `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteEtaleSpecialization_coordinates`;
- `AlgebraicGeometry.Etale.FiniteSmoothPurity.ordinaryFiniteUnitPullback_eq_unitCoordinates`;
- `AlgebraicGeometry.Etale.FiniteSmoothPurity.rankZeroBundleSection_coordinates`;
- `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteRankZeroNormalIntegration_coordinates`.

Every private helper is proved. There are zero `sorry` occurrences in the five
Lean files. Holes closed: one. Holes added: zero. Unfinished statements split off:
zero. Existing component obligations, including bundle-section purity-unit
normalization and rank-zero affine normalization, are reused without restatement.

## No longer needed

No original Lean import is removed and no module is withdrawn. No adopted
source-library declaration is removed or changed.

The planned fresh clopen/Rees computation and proof that the normal projection is
an isomorphism are unnecessary here: Geometry 0 supplies the smooth rank-zero
deformation projection, and base change supplies the needed etaleness of the
normal projection. The existing normalized sum-adjunction exchange computes the
actual fibre mates. The normalized bundle orientation and its rank-zero theorem
replace a fresh frame-by-frame calculation of the integration trace.
`VectorTraceGeometricDescent` and `VectorIntegrationRankZeroLocal` need no new
direct proof import in this item.

The item's original direct proof dependencies
`lem-pur-etale-support-map-compatibility` and `def-amb-vector-integration` are
replaced by the proved factor nodes and the geometry package. Their constructions
remain needed transitively; this is not a global withdrawal request. The unit's
statement and route are preserved.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged. The original DAG plan repeats normalization work
already available in `EtaleSumRightAdjointCoherence`,
`FiniteRingBundleSectionOrientation`, and the coefficient-unit comparison lemmas.
The proof reuses those declarations for arbitrary finite A, including zero
coefficients and empty schemes. No field, connectedness, nonempty-sheet or
positive-rank hypothesis is added.

The specialization proof imports the already proved private `mateTransport`,
`derivedAdj_eq`, `sum_baseChange`, normalized comparison, and pullback-unit
coherence helpers through `import all`. Their signatures apply to arbitrary finite
A, even where their source modules also contain specialized coefficient theorems.
The coefficient-unit conversion is proved in arbitrary coefficient categories
before module specialization to control repeated kernel conversion costs.

## New nodes

`lem-pur-finite-etale-specialization-coordinates` records the normalized Rees
specialization preserving section coordinates. It contains no integration factor.

`lem-pur-ordinary-finite-unit-coordinate-identification` records equality of the
canonical ordinary coefficient pullback and monoidal unit comparison. It is proved
from the existing constant-unit square and ordinary constant-pullback comparison.

`lem-pur-rank-zero-bundle-section-coordinates` records the normalized
identity-adjunction comparison for a rank-zero bundle, independently of its
integration trace and any Rees family.

`lem-pur-finite-rank-zero-normal-integration` records integration and the actual
cone comparison preserving the unit coordinates. It has no kappa or specialization
hypothesis. All four nodes lie in `sec-smooth-purity`, unit
`sk-thm-purity-transport`, and all four Lean statements are proved.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteEtaleSectionIntegration": "5ec59722c2e6021dd9a964a0fc4057d202de3e2e", "Sheaf.Paper.FiniteEtaleSpecializationCoordinates": "254d1a014da0f379c5cb573613187129b5660023", "Sheaf.Paper.FiniteRankZeroNormalIntegration": "22e8e4f310d0e1afc30097fedde04940e1636faa", "Sheaf.Paper.FiniteUnitCoordinateIdentifications": "e77819042ce53a1a89909b7a0e9785333e695a09", "Sheaf.Paper.RankZeroBundleSectionCoordinates": "43fdd114eecc7608913403b44561ae89e69e124c"}, "results": {}, "time": "2026-10-28T01:05:49+0800", "transitive": 0, "version": 1}
```

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
