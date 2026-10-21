# AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleBraiding

## Reason

The rework row records a cluster quarantine of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided`.
Restore its archived source at the original library path, preserving its declarations and
dependencies. The archive already compiles on the current published build. This repairs
the missing source module without altering any definition or target meaning.

## Old

The library source path is absent. The preserved quarantine source declares:

```lean
set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance monoidalCategory_boundedConstructible
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] :
    MonoidalCategory (Dᵇc(X.left)⟦Λ⟧) :=
  inferInstance

attribute [local instance] DerivedCategory.braidedCategory' in
@[instance_reducible]
noncomputable def boundedConstructibleBraiding
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)] :
    BraidedCategory (Dᵇc(X.left)⟦Λ⟧) :=
  ObjectProperty.fullBraidedSubcategory _
```

The displayed declarations share the archive's variables:

```lean
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
```

## New

The entire archived source is restored verbatim to
`lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructibleBraided.lean`.
The declarations, their variable context, imports, documentation, attributes, and bodies
are exactly as in the quarantine source. The archive itself is unchanged.

## Users

`tools/downstream.py` cannot inventory a missing source module and reports it unknown.
Exact import and declaration-name searches in both the library and the quarantine give
the following consumers. No consumer needs an adaptation: the archived API is restored
unchanged. Quarantined consumers remain the responsibility of their own rework items.
`Slop.Basic` and quarantined `TraceFormula.Statement` compile against the restored module.
Quarantined `PoincareDuality.Verdier` has identical errors with and without the restoration:
unknown `projectionDerivedMonoidal` and `projectionCoefficientMonObj`, followed by an
unsolved goal. It is not adapted in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Direct public importer; API restored. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Quarantined direct importer and braiding user; API restored. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Quarantined direct importer and braiding user; API restored. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Uses the restored braiding through Slop.Basic. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Uses the restored braiding through Slop.Basic. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Uses the restored braiding through Slop.Basic. |

## Status

landed 20261021T014713-L-2446470 2026-10-21 (merge of deliver/K1/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided)
