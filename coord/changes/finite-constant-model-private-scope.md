# FiniteConstantModel private proof scope

## Reason

The proof introduces a `FreeModels` section for private helpers. The static interface
checker records the two section-local variable commands as an interface change.
These variables are scoped by the section and used only in private declarations.
Existing public signatures, definitions, visibility, instances, and public imports are identical.

## Old

No `FreeModels` section between `HasResolution` and the coefficient declarations.
The existing coefficient variables there are:

```lean
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
```

## New

A section containing only private helpers is inserted before the unchanged coefficient variables:

```lean
section FreeModels
variable (A : Type u) [CommRing A]
-- private scalar and categorical helpers
variable [TopologicalSpace A] [IsTopologicalRing A]
-- private exactness and finite-free helpers
end FreeModels
```

No public declaration is altered by these section variables. The only interface diagnostic
is `(commands such as variable, open, notation or attribute)`; comparison of every existing
public declaration reports no changed name.

## Users

The public API and both direct importers were read. No consumer adaptation is necessary:
section variables do not survive the section or change imported declarations.
There is no changed declaration for a downstream `--uses` query; the conservative `--uses A`
query is recorded separately in the worker session.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteConstantModelResolution | V6 | private proof scope only |
| Sheaf.Paper.InternalHomDualConstructibleModels | not adapted | same public signatures and definitions |
| Sheaf.Paper.ConstructibleInternalHomContinuity | not adapted | same public signatures and definitions |

All transitive consumers see the identical public API, so none needs editing.

## Status

landed 20261019T034327-L-421700 2026-10-19 (merge of deliver/V6/Sheaf.Paper.FiniteConstantModelResolution)
