# Finite coefficient canonical projection predicates

## Reason

Bundle the native adjunction, tensor bifunctors, and pullback tensor comparison in
ProjectionContext so their large resolving-instance arguments are constructed once.
The bundled contexts are genuine structures with each field constructed from the
existing native construction. Both predicate definitions now use ProjectionContext.projection.
The existing iff lemmas retain exactly their old public statements and are proved by
unfolding the corresponding context and rfl, certifying that both predicates are still
invertibility of exactly the published canonical arrows. No target meaning changes.
The new public import is necessary for these two definition bodies.

## Old

```lean
def finiteCoefficientProjectionIsIso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj R Y))) : Prop :=
  IsIso ((((derivedUpperStarLowerStarAdjunction R p).rightAdjointProjectionMap
    (T_C := derivedTensor R X) (T_D := derivedTensor R Y)
    (leftDerivedUpperStarTensor R p)).app K).app M)

def ordinaryFiniteCoefficientProjectionIsIso
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) : Prop :=
  IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app K).app M)
```

## New

```lean
def finiteCoefficientProjectionIsIso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj R Y))) : Prop :=
  IsIso ((internalProjectionContext R p).projection K M)

def ordinaryFiniteCoefficientProjectionIsIso
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) : Prop :=
  IsIso ((ordinaryProjectionContext A p).projection K M)
```

## Users

Repository search and tools/downstream.py --uses identify the two direct users below.
All other module descendants use these predicates transitively. The context is locally
irreducible globally only through its own @[irreducible] definition; the old iff API
provides the public equation, so consumers need not unfold the context.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteCoefficientProjectionEncoding | H7 | Predicate signatures and iff signatures retained; definition bodies use native context bundles. |
| Sheaf.Paper.FiniteProperBaseChange | done, unclaimed | Uses the same projection_encoding iff and canonical-map iff; no adaptation needed. |

The unchanged entire FiniteProperBaseChange consumer was compiled against the packet
in 35.2 seconds using a temporary module copy; it was then removed.

## Status

landed 20261025T202221-L-2695356 2026-10-25 (merge of deliver/H7/Sheaf.Paper.FiniteCoefficientProjectionEncoding)
