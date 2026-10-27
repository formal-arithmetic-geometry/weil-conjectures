# AlgebraicGeometry.Etale.compactSupportGraphSheafComparison_normalization_transpose

## Reason

Complete the graph normalization proof using private constructions and proved helpers.
The delivery preflight requests a change record for additional scoped commands and
instances in the module. All six helper propositions are private proved theorems, registered with local
instance attributes. Their
instance attributes, the irreducibility attributes and the elaboration options are
limited to the proof namespace or file scope. No public theorem signature, public
import, target definition or source-library declaration changes.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
```

The module had no `GraphNormalization` helper namespace. Its transpose theorem
had the same signature as now and proof `by sorry`.

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite
```

The proof adds namespace `GraphNormalization` with private helper theorems
registered as local instances
`section_open`, `section_closed`, `section_comparison_iso`, `siteBC_iso`,
`restrictionBC_iso`, and `toTest_open`. It marks its explicitly constructed
comparison functors and natural transformations locally irreducible to control
elaboration, and uses scoped backward elaboration options for the diagram
calculations. These declarations are implementation details of the proof.
All existing public declaration signatures remain verbatim.

The repair of return `322e42761b2` removes the four reported duplicate helper
declarations. Pullback projection identities are supplied directly by Mathlib;
the definitional graph-map equation and the application of the Mathlib
left-adjoint-uniqueness unit law occur only inside their consuming proofs.
The other module's similarly named declarations are private and unavailable by name
to importers, as verified by a compiler probe. No new public API is introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization | G5 | Sole edited Lean module; fills its original hole. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unmodified consumer | Existing public theorem signatures and public imports are unchanged; no adaptation. |

## Status

landed 20261024T014842-L-2286031 2026-10-24 (merge of deliver/G5/Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization)
