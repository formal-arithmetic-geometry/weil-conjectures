# etaleConstantModuleFunctor_isEquivalence

## Reason

The unchanged target hypercover_cohomology_module_part assumes Ring R. Its planned
constant-coefficient realization API required CommRing, although its construction
uses only RingCat, left modules, scalar restriction and module sheafification.
The module was unclaimed when inspected. Replacing its single section variable
with Ring compiles the same explicit construction and all its proofs.

## Old

```lean
variable (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
```

This context applies to etaleConstantModuleRing, etaleConstantModulePresheaf,
etaleConstantModuleRealization, etaleConstantModuleFunctor,
etaleConstantModuleUnderlyingIso, etaleConstantModuleRestriction,
etaleConstantModuleRestrictionFunctor, etaleConstantModuleUnitIso,
etaleConstantModuleCounitHom, etaleConstantModuleCounitHom_underlying,
etaleConstantModuleCounitIso and etaleConstantModuleFunctor_isEquivalence.
Their declaration texts are unchanged.

## New

```lean
variable (Y : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
```

Every definition has exactly its previous value at a commutative ring; this adds
noncommutative left-module instances. It changes no meaning of any target or
existing commutative caller. No existing caller requires an adaptation.

## Users

The downstream.py --uses search covered all twelve declarations. Its direct users
are exactly the following three existing modules; all transitive users retain
identical specializations. The new injective-row module is also listed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence | unclaimed | The single binder generalizes all twelve declarations; same bodies and proofs. |
| Sheaf.AlgebraicGeometry.InjectiveEtaleConstantRingModule | unclaimed | Existing CommRing specialization unchanged; no edits. |
| Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian | unclaimed | Existing CommRing specialization unchanged; no edits. |
| Sheaf.Paper.HypercoverInjectiveModuleRow | N3, new | Uses the stronger API for Ring R. |

The node statement_change records every existing DAG citer. All their uses still
hold. Nothing in Challenge.lean is edited.

## Status

landed 20261015T233749-L-3369289 2026-10-15 (merge of deliver/N3/Sheaf.Paper.HypercoverCohomologyModule)
