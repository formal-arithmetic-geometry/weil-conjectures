# FiniteClopenDerivedDecomposition private scalar-instance context

## Reason

The source-overlay compile of this item stopped in the current dependency
`Sheaf.Paper.FiniteClopenDerivedDecomposition` with:

```text
FiniteClopenDerivedDecomposition.lean:61:22: error(lean.unknownIdentifier):
Unknown constant `AlgebraicGeometry.Scheme.ProEt.ClopenScalar.derived`
```

The same attribute block names `ClopenScalar.sheafify` and
`ClopenScalar.locallyBijective`. Their public owner is
`Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarData`; the smaller support
interface no longer exposes that owner transitively. The module is unclaimed in
both the local and current server claim records checked during this session.

## Old

```lean
import all Sheaf.Paper.FiniteClopenDecompositionCore
```

The attribute block later in the file already excludes the three scalar instances.

## New

```lean
import all Sheaf.Paper.FiniteClopenDecompositionCore
import Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarData
```

The added private import makes those existing instance names available to the
existing exclusions. All theorem statements, proofs, definition bodies, public
imports and public attributes are unchanged. This is a proof-context repair;
it introduces no mathematical assumption or hole and changes no target meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences | unclaimed in checked records | Same public interface. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed in checked records | Same public interface. |
| Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences | unclaimed in checked records | Same public interface. |
| Sheaf.Paper.ClopenCommonCompactSupport | unclaimed in checked records | Same public interface. |
| Sheaf.Paper.ClopenRoosIntegralDescent | unclaimed in checked records | Same public interface. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed in checked records | Same public interface. |
| Sheaf.Paper.VaryingDimensionDualizingInverse | P4 | Main item; compiled against the repair. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed in checked records | Same public interface. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed in checked records | Same public interface. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed in checked records | Same public interface. |
| Sheaf.Paper.ClopenIntegralRestriction | unclaimed in checked records | Same public interface. |

No consumer source is adapted by this change.

## Status

landed 20261027T180726-L-3895569 2026-10-27 (merge of deliver/P4/Sheaf.Paper.VaryingDimensionDualizingInverse)
