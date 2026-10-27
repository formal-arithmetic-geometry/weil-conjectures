# WeilConjectures.ConstructibleExceptionalCoefficients.exists_rational_common_exact_shifts

## Reason

The delivery checker flags changes to `attribute` commands as potentially visible
interface changes. This delivery adds only local elaboration settings and private
proof imports. The public theorem signature, the full text of
`RationalCommonShiftData`, and the existing public import remain unchanged.

The settings keep scalar-localization categories and coefficient constructions
from expanding during alias comparisons. Together with abstract finite-field
parameters, named normalization helpers, and the proved support module, these
bring each file below the 60-second limit. No global attribute or instance changes.

## Old

```lean
attribute [local irreducible] HasDerivedCategory.standard Padic

theorem exists_rational_common_exact_shifts :
    Nonempty (RationalCommonShiftData.{u, v} l Ω D hl A P) := by
  sorry
```

## New

The theorem's signature is verbatim identical; its complete reduction is in the
item module. The proof-local settings in that module are:

```lean
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category CategoryTheory.ScalarLocalization.composition
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  WeilConjectures.sfRationalScalarExtension WeilConjectures.sfRationalConstructibleLocalization
  WeilConjectures.sfRationalScalarComp
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.scalarAssociator

attribute [local instance 2000] Shrink.instField
```

`backward.isDefEq.respectTransparency.types` is set to `true`; no transparency
respect option is disabled. The two new imports of the item are proof-only imports.
No definition used by a target has changed its mathematical meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExceptionalCommonStageFromRational | unclaimed in the shared claim snapshot | The structure and theorem interface are unchanged. The delivery tool attempted this direct importer and reported `INFRA (73 s)`, rather than a certified pass; no regression compiler message was provided. No adaptation is included. |

There are no existing importers of the new support and scalar-square modules.
The item is their first consumer. There are no forced adaptations.

## Status

landed 20261027T234403-L-122010 2026-10-27 (merge of deliver/Y3/Sheaf.Paper.ExceptionalRationalCommonExactness)
