# Sheaf.Paper.LocalFrobeniusTrace compilation settings

## Reason

The completed return proofs initially caused the file to exceed the 60-second file
limit. Profiling found substantial typeclass/unification work with the original
file-wide `backward.isDefEq.respectTransparency false`. The normal setting compiles
much faster; the two private pullback lemmas need the original setting to identify
the geometric fibre with the chosen pullback object during rewriting.

The complete file compiles cleanly in 13.5 seconds after scoping the old setting to
those two private lemmas. These options control this file's elaboration and linting;
they are not exported to importing modules. Existing public signatures, definition
bodies, attributes, and public imports are verbatim unchanged. There is no change to
the meaning of any target statement or any consumer's statement.

The unused-section-variable linter is disabled in this file because the retained
finite-type assumptions in localClosedPoint_compatible's existing signature are not
used by its completed proof. Removing those assumptions would change the signature.

## Old

The original file-wide settings were:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
```

The five theorem bodies were `by sorry`. There were no private power/projection/lift
helpers and no explicit private import of `WeilConjectures.PointCount`.

## New

The file-wide settings are:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
```

Each of the two completely proved private theorems
`localFrobeniusPower_projections` and `localLift_return` is preceded by:

```lean
set_option backward.isDefEq.respectTransparency false in
```

Added the completely proved private theorem `localPointPower_eq` and the private
proof import `import WeilConjectures.PointCount`. All five public theorem proofs
are complete. No public declaration signature or definition body is changed.

## Users

The following is the full transitive consumer list from
`python3 tools/downstream.py Sheaf.Paper.LocalFrobeniusTrace --names`, plus the item.
Options have file scope, and the new helpers are private, so every consumer sees
identical public declarations and instances. No consumer adaptation is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.LocalFrobeniusTrace | A8 | Five holes closed; compilation settings scoped. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | K8 | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Identical public API and definitions; no adaptation. |

## Status

landed 20261021T100736-L-4128872 2026-10-21 (merge of deliver/A8/Sheaf.Paper.LocalFrobeniusTrace)
