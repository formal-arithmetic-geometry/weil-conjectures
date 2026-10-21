# Sheaf.Paper.LocalFrobeniusTrace elaboration settings

## Reason

The current item source contains five theorem holes. Completing their proofs needs
identification of the geometric fibre with its defining pullback in two private
helpers. Keep the original transparency option for those helpers, and use the
normal transparency setting elsewhere to avoid unnecessary unfolding of the large
coefficient constructions. The earlier A8 change record identifies this same
elaboration issue, but its five proofs are absent from the current source.

The elementary proof of localClosedPoint_compatible does not use the section's
finite-type assumptions. Suppress the unused-section-variable linter only for
that theorem, preserving its existing signature. No exported option, public
signature, definition body, public import, or target meaning changes. Every new
helper is private and proved.

## Old

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
```

The five public theorems have proofs `by sorry`. There is no explicit private
proof import of WeilConjectures.PointCount and no private power/projection/lift
helper.

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
```

Before each of localFrobeniusPower_projections and localLift_return:

```lean
set_option backward.isDefEq.respectTransparency false in
```

Before localClosedPoint_compatible:

```lean
set_option linter.unusedSectionVars false in
```

The five theorem proofs are complete. The private helper localPointPower_eq
identifies positive point powers with Spec of field powers. Added the private
proof import `import WeilConjectures.PointCount` for the residue-field structure
map equation. All existing public declarations and definitions are preserved.

## Users

The following transitive consumers are the output of
`python3 tools/downstream.py Sheaf.Paper.LocalFrobeniusTrace --names`, plus the
item. These settings concern only this module's elaboration; no consumer is
adapted and every consumer's meaning is unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.LocalFrobeniusTrace | Z5 | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | H1 | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Identical public API and definitions; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Identical public API and definitions; no adaptation. |

## Status

landed 20261021T144034-L-39802 2026-10-21 (merge of deliver/Z5/Sheaf.Paper.LocalFrobeniusTrace)
