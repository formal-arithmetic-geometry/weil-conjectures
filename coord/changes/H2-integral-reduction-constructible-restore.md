# integralReduction_boundedConstructible proof-context restoration

## Reason

The assigned quarantined module fails at destructuring `integralConstructible_serre`
after upstream synchronization. The closure predicates and the proved Serre-based
triangulated instance now live in a relocated proof API. Restore the complete archive
and import that API privately. No definition or theorem signature changes.

## Old

The archived import list has no import of
`Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.
The failing proof context is:

```lean
  obtain ⟨hk, hc, he⟩ := integralConstructible_serre ℓ E X
  have := hk
  have := hc
  have := he
```

## New

Add the proof-only import:

```lean
import Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
```

Replace that proof context with explicitly typed instances and explicitly select
the proved weak Serre theorem:

```lean
  let : ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R) :=
    (integralConstructible_serre ℓ E X).1
  let : ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R) :=
    (integralConstructible_serre ℓ E X).2.1
  let : ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R) :=
    (integralConstructible_serre ℓ E X).2.2
  let : (boundedConstructible R).IsTriangulated :=
    isTriangulated_boundedConstructible_of_serre R
```

Every archived declaration and construction is retained. The theorem signature,
public imports and target meanings are identical. This record documents a proof
repair, not an interface or definition change.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralReductionConstructible | H2 | Assigned restoration and proof-context repair; zero local holes. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed in the shared claim snapshot; quarantined | Sole direct importer; theorem application unchanged, no adaptation. |

The direct-import and declaration-use search includes both `lean/` and `quarantine/`.
All indirect users see the same public theorem and public import closure.
A separate consumer of the unchanged theorem statement compiles with the standard scoped object instances and the
Profinite size instance already used by IntegralResidueExchange.

## Status

landed 20261020T154617-L-3136528 2026-10-20 (merge of deliver/H2/Sheaf.Paper.IntegralReductionConstructible)
