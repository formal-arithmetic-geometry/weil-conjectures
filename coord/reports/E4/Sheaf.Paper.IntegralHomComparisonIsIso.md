## What changed

Replaced the sole `sorry` in `Sheaf.Paper.IntegralHomComparisonIsIso`,
`WeilConjectures.IntegralHom.comparison_isIso`, by a complete Lean proof from two
strictly smaller statements. Its signature and public import are unchanged.

The proof obtains an explicit signed chain representative, proves every component
invertible using the two-term free coefficient calculation, localizes that
isomorphism, and uses the normalization square to identify the restricted specified
comparison. It then proves conservativity of ordinary scalar restriction by
composition with the forgetful functor to sheaves. Exactness identifies its
cohomology maps with the cohomology maps of derived restriction. Reflecting those
isomorphisms and applying the derived cohomology criterion finishes the proof.
The last conservativity argument is proved here, not left as a new obligation.

Added `Sheaf.Algebra.Homology.TwoTermFreeHomTensorComponents` with the explicit
predicate `IsSignedHomTensor` and the component theorem. Added
`Sheaf.Paper.IntegralHomComparisonRepresentative` with the chain representative
and its normalization square. The first statement has no reduction presentation
or derived categories; the second has no assertion of invertibility. Their
combination is the actual argument in the item, rather than an application of a
renamed copy of its conclusion. Both new theorem docstrings contain the source
and full mathematical proof. The signed-evaluation predicate is an actual formula,
with no postponed data construction.

Updated the item's proof route and supplied two new DAG nodes. No other existing
module or node is changed. A declaration-scoped removal of the generic
`hasSheafify_of_essentiallySmall` instance avoids successor-universe inference
conflicting with the existing sheafification at `max u (t + 1)`; it exports no
instance change.

Validation: all three delivered Lean modules compile in import order via
`lcompile.py --all`. The last run took 0.1 s, 3.8 s and 6.0 s, respectively.
All delivered Lean lines satisfy the 100-character limit. Zero inputs, the empty
scheme/site, the zero ring in the algebra calculation, n=0, and arbitrary
unbounded Hom inputs were checked mathematically against the statements.

## Proved and sorry left

This is a decomposition, not a net reduction of proof holes.

Closed one original hole:

- `WeilConjectures.IntegralHom.comparison_isIso`
  (`lem-sf-integral-hom-comparison-is-iso`). Its proof has no `sorry`.

Added two holes, one per new module:

- `WeilConjectures.IntegralHom.twoTermFreeHomTensor_component_isIso`
  (`lem-sf-two-term-free-hom-tensor-components`). The finite two-factor/product
  calculation remains to be formalized.
- `WeilConjectures.IntegralHom.comparison_representative`
  (`lem-sf-integral-hom-comparison-representative`). The quotient-resolution,
  signed chain map and evaluation-normalization calculation remain to be
  formalized.

Thus the item goes from one hole to zero; the packet closes one and adds two,
for a net increase of one hole. There are no other new holes, no holes inside
any definition and no arbitrary witness selected into a definition.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SplitPerfectTensorKInjective`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Mathlib.CategoryTheory.Yoneda`

The valuation, completion, resolution and split-free tensor results still occur
in the new representative node's proof plan. Scalar restriction is already
available through the unchanged public statement dependency. Removed unused
private proof imports from the representative after testing its statement.
Neither a generic exact-restriction theorem for internal Hom nor Yoneda is needed
in the final conservativity argument: underlying sheaf conservativity and
cohomology supply it directly.

No existing node or module is asserted globally unnecessary, and none is
withdrawn. The original mathematical coefficient route is retained through the
representative node. No unit-level statement or step is bypassed. No maintainer
`tool_uses` approvals were removed.

## Where the brief, the DAG or earlier work was wrong

The node's plan does describe the mathematical argument, but the already stated
DVR, quotient, tensor and scalar-adjunction results do not themselves provide the
actual signed Hom-tensor map or its normalization against the specified
comparison. These are genuine glue steps, now isolated with precise statements.

The already proved `SitePerfectScalarHomComparison` and the perfect-ring Hom
comparison require a perfect Hom source. They cannot be applied to the arbitrary
K of this item. The general rigid-library comparison found in the source library
requires an invertible coefficient object, whereas the quotient complex here is
merely perfect. Reusing those results would add an unjustified hypothesis.
Mathlib searches found general reflection lemmas used by the proof, but no theorem
covering this signed, unbounded sheaf calculation. The independent scheme and
coefficient universes are retained; some existing generic chain-level lemmas use
one common universe, which will need the appropriate transport when formalizing
the representative.

No statement is disputed, weakened or changed, and the unit's route is unchanged.

## New nodes

`lem-sf-two-term-free-hom-tensor-components`, in
`dag/nodes/sec-six-functors/lem-sf-two-term-free-hom-tensor-components.json`,
states degreewise invertibility of any chain map satisfying the explicit signed
local evaluation formula when the coefficient complex has two unit terms. The
proof reduces to a two-factor biproduct commuting with a product over all source
degrees, with an involutive sign on one coordinate. It imposes no finiteness on
the Hom source and does not mention the integral comparison.

`lem-sf-integral-hom-comparison-representative`, in
`dag/nodes/sec-six-functors/lem-sf-integral-hom-comparison-representative.json`,
states the signed chain representative and endpoint isomorphisms identifying its
localization with the specified reduced comparison. It does not assert the map
or its components are invertible; that comes only from the other node. Both new
nodes cite the current blueprint proof, inherit the item's chapter and unit, and
record the actual LeanFinder, Loogle, Mathlib grep and LeanSearch queries.

There are no change records because no existing statement, definition or public
interface was changed.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 4 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.Algebra.Homology.TwoTermFreeHomTensorComponents": "13714c05013d53599c8749ebb21efd8d716f5161", "Sheaf.Paper.IntegralHomComparisonIsIso": "e2cb2dcc4edc7cdd17e69418565c98fdaa5f8a30", "Sheaf.Paper.IntegralHomComparisonRepresentative": "2e6173be1f203203891b0648b96a370b88230b74"}, "results": {"Sheaf.Paper.GeneralHomComparisonCocycles": {"hash": "d868c7f7d9bcfda76be62f0fec6e271641b39e6e", "status": "OK"}, "Sheaf.Paper.IntegralHomReduction": {"hash": "a2d05524c834750b5f29348b20ab0cc22d6bce8d", "status": "OK"}, "Sheaf.Paper.IntegralHomReductionTowerComponents": {"hash": "a873597aeba586a978fa66fb6aa048677721041e", "status": "OK"}, "Sheaf.SixFunctors.IntegralVerdier": {"hash": "26cc57e04421a4b0121abccdc539c11c22af323a", "status": "OK"}}, "seconds": 38, "time": "2026-10-28T06:47:52+0800", "transitive": 0, "version": 1}
```

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
