# supportRefinement_isIso proof normalization

## Reason

Complete the finite-origin invertibility proof while keeping large native
support-model constructions out of definitional conversion. The new local
irreducibility attribute affects only elaboration in this module; existing public
statements, definitions, visibility, and exported attributes remain unchanged.

## Old

There was no local irreducibility attribute on these four definitions.
The theorem `WeilConjectures.PurStrictScalar.supportRefinement_isIso` had proof
`by sorry`.

## New

Immediately after the unchanged definition `supportRefinement`:

```lean
attribute [local irreducible] supportRefinement supportModel reduction compositionC
```

Two proved private helpers identify `refinementComparison` with `compositionC`
and transport component invertibility through a whole natural-transformation
conjugation equality. The public theorem applies those helpers to the unchanged
`supportRefinement` construction and `refinementComparison_isIso`.

## Users

There is no public interface or definition change, so no downstream adaptation is
required. All new declarations are private and the attribute is local.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportStrictScalarRefinement | V7 | Proof completion and local elaboration control only. |

## Status

landed 20261025T124154-L-1942404 2026-10-25 (merge of deliver/V7/Sheaf.Paper.CompactSupportStrictScalarRefinement)
