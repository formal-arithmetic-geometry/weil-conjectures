# CategoryTheory.CochainPullback.moduleUnit

## Reason

The proof makes `SheafOfModules.monoidalCategory` locally irreducible to avoid
unnecessary unfolding. The explicit coefficient unit must reduce when
elaborating `moduleUnit`; `ExistsUnique` must also reduce for `Classical.choose`.
The original definition body is retained verbatim. Only local elaboration
settings surround it; no transparency attribute is exported.

## Old

```lean
noncomputable def moduleUnit (f : RingedPullback R S) (k : Comparison f) :
    f.L.obj (𝟙_ (Modules R)) ≅ 𝟙_ (Modules S) :=
  Classical.choose (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_unit
    R S f.RI f.uInv f.I f.coefficient f.L f.hobj f.hmap k)
```

## New

The definition body above is unchanged. Its new local elaboration context is:

```lean
attribute [local semireducible] SheafOfModules.monoidalCategory
set_option backward.isDefEq.respectTransparency false in
```

The scoped option precedes the definition and its docstring. The module monoidal
structure is made locally irreducible again afterwards. These settings affect
elaboration in this file only; they export no transparency attribute.

## Users

The refreshed `tools/downstream.py` scan finds 28 downstream modules.
`CochainCoefficientArrows` is the direct importer. The actual external users of
`moduleUnit` include `CochainComparisonMonoidalEquations`, whose
`module_right_unit` uses the original unique-existence choice predicate.
`CochainPullbackTensorCoherence` uses the lifted unit and comparison.
The last-segment hits in `ContinuousRationalDerivedRealization`,
`RationalDirectImageRealization` and the two `FiniteAdic*SectionData` modules
refer to another namespace. `ExternalRHomConePairing.pull` is likewise unrelated.

The original direct consumer `CochainCoefficientArrows` compiles against the
new artifact in 24.1 seconds. After the next green build, the unchanged higher
consumers `CochainComparisonMonoidalEquations` and `CochainPullbackTensorCoherence`
compile against the new artifact in 31.0 and 29.2 seconds respectively.
No consumer is adapted. The temporary `.exists` projection was removed before
delivery; the original selected object and its definitional formula are retained.
The proof also keeps its private unit constructions unexposed, as no module
imports these private helpers. This changes no public definition or signature.

## Status

landed 20261020T145450-L-2398089 2026-10-20 (merge of deliver/B9/Sheaf.SecSmoothPurity.CochainTensorCoherenceData)
