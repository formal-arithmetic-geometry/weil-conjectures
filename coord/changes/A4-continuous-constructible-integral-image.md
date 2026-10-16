# AlgebraicGeometry.ProEtale.CondensedRing.continuousConstructible_integral_image_triangulated

## Reason

Group A4 holds this module. The new proof lifts rational arrows after multiplying by a power
of ℓ, then compares distinguished triangles. Four new modules and their DAG nodes record the
coefficient telescope, denominator calculation, bounded-source reduction and remaining
sheaf-source input. No other existing module is edited or adapted.

The static interface check detects additional `open` and `open scoped` commands, local
irreducibility attributes on `Functor.leftDerivedFunctor` and `Functor.mapDerivedCategory`,
and relocation of the `FiniteDimensional` variable declaration. These commands support private
proofs only. The irreducibility attributes are local to this module and prevent accidental
unfolding of derived-functor constructions. The namespaces and scopes resolve triangle, tensor
and zero-object notation. Finite dimensionality is declared immediately before the original
public theorem, retaining its original signature; the preceding private invertibility helpers
do not need that hypothesis. All new helpers in the existing module are private and proved.

## Old

The original public declaration has ambient variables
`(ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]`
and `[FiniteDimensional ℚ_[ℓ] E]`:

```lean
theorem continuousConstructible_integral_image_triangulated (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] :
    (((ProEtale.boundedConstructible (condensedRingObj (integralCoeff ℓ E) X)).ι ⋙
      integralScalarExtension ℓ E X).essImage).IsTriangulated
```

Its proof was `by sorry`.

## New

The same ambient variables and public signature are retained verbatim:

```lean
theorem continuousConstructible_integral_image_triangulated (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] :
    (((ProEtale.boundedConstructible (condensedRingObj (integralCoeff ℓ E) X)).ι ⋙
      integralScalarExtension ℓ E X).essImage).IsTriangulated
```

The proof now uses the proved denominator-clearing theorem and private triangle and
invertibility helpers. The original public coefficient import is unchanged; the new
denominator import is a normal proof import. No exported instance, definition, notation,
attribute, signature, target or blueprint unit is changed.

## Users

`tools/downstream.py Sheaf.Paper.ContinuousConstructibleIntegralImage --uses
continuousConstructible_integral_image_triangulated` lists the item and integral-model module
as textual declaration users, and the other modules below as transitive importers.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ContinuousConstructibleIntegralImage` | A4 | Proof replaced; signature unchanged. |
| `Sheaf.Paper.ContinuousConstructibleIntegralModel` | unclaimed | Direct use; unchanged signature, no adaptation. |
| `Sheaf.Paper.ContinuousExchangeIntegralModel` | unclaimed | Transitive importer; no API change or adaptation. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | Transitive importer; no API change or adaptation. |
| `TargetsCheck` | unclaimed | Transitive importer; no API change or adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | Transitive importer; no API change or adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | Transitive importer; no API change or adaptation. |

## Status

landed 20261016T024743-L-1401577 2026-10-16 (merge of deliver/A4/Sheaf.Paper.ContinuousConstructibleIntegralImage)

The original hole is reduced to one strictly narrower geometric hole: sequential Hom
continuity with a constructible sheaf source in degree zero. All formal reductions have
complete Lean proofs; no net decrease in the sorry ledger is claimed. All five delivered
modules compile through the prescribed launcher. Validation is by `deliver3.py --no-push`;
independent second reading is recorded in report.md under `## Second reading by A4`. No forced adaptations are needed.
