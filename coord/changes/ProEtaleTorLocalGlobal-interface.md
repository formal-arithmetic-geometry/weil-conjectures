# Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal command scope

## Reason

The proof adds private helpers inside a named section, with local elaboration options
and an additional namespace opening. The stage-3 preflight conservatively identifies
these command additions as a possible importing interface change. Both original public
imports, the restriction definition, and the theorem signature and visibility are unchanged.
There is no change to the meaning of a target statement.

## Old

The original command block following the public section was:

```lean
set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
```

After the `CategoryTheory` namespace containing `coefficientModelSliceRestriction` ended,
the original file immediately opened `namespace AlgebraicGeometry.Scheme` for the theorem.

## New

The original command block and both public imports are retained verbatim. Between the
restriction definition and the final theorem, the proof inserts this helper section:

```lean
section ProofHelpers
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MonoidalCategory
```

All declarations in this section are private and proved. The section ends before the
original theorem's namespace is reopened, so these proof options and the opening are
scoped to the helpers. The public declarations
`CategoryTheory.coefficientModelSliceRestriction` and
`AlgebraicGeometry.Scheme.hasFiniteCoefficientProEtaleTorAmplitude_iff_locally`
retain their existing signatures and visibility. Only private proof imports are replaced.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | unclaimed | Direct importer; the two public declarations and public imports are unchanged. No adaptation is required. |
| `Sheaf.Paper.IntegralModels` | unclaimed | Transitive importer; the public interface is unchanged. No adaptation is required. |

The users were enumerated with `tools/downstream.py` on the current shared source.

## Status

landed 20261019T112549-L-3955856 2026-10-19 (merge of deliver/U7/Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal)
