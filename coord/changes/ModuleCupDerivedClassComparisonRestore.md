# AlgebraicGeometry.Scheme.Modules.exists_cupDerivedClassComparison

## Reason

Restore the assigned comparison module after the failed landing recorded in its repair note.
Its dependency's conflicting local instance has already been given a unique name in the
published library. The complete restored proof now compiles without editing any dependency.

## Old

The assigned module is absent from the current base after transactional removal of the failed
landing. The prior failed source, preserved verbatim in the repair note, has these public
signatures (under its unchanged universe and derived-category assumptions):

```lean
abbrev cupDerivedSections (F : X.Modules) :=
  (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)

/-- A comparison with derived global sections, including the representative formula.
The cycles in integer degrees are obtained by the actual extension by zero. -/
structure CupDerivedClassComparison where
  equiv : ∀ (F : X.Modules) (n : ℕ),
    (RingedSpace.moduleCohomology X.toRingedSpace n).obj F ≃ₗ[Γ(X, ⊤)]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) (n : ℤ)).obj
        (cupDerivedSections X F)
  on_cycles : ∀ {F : X.Modules} (D : CupAcyclicResolution F) (n : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K),
    let K := ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj D.integerComplex
    ∃ z : K.cycles (n : ℤ),
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).map
        (D.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom) (K.iCycles n z) =
          a.val ∧
      equiv F n (D.class n a) =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) (n : ℤ)).map
          (moduleCup_globalComparison X D.integerComplex ≫
            (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
              (inv D.derivedAugmentation))
          (cupLocalizedCycleClass K n z)

theorem exists_cupDerivedClassComparison : Nonempty (CupDerivedClassComparison X)
```

The former local coefficient-ring instance was anonymous:

```lean
@[instance_reducible] local instance : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
```

## New

Restore exactly the interface and abbreviation body displayed under Old, with the complete
proof of `exists_cupDerivedClassComparison`. Remove only the redundant proof import of
ExtendMap and a redundant `by exact` tactic block. No mathematical public signature changes. Give the local coefficient-ring instance an
explicit module-specific name, with identical type and body:

```lean
@[instance_reducible] local instance cupDerivedClassCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
```

This retires its generated anonymous instance constant name. There are no current importers
or uses of that generated name; the coefficient-ring value and instance visibility are unchanged. The
companion homology module is used unchanged, without replacing its existing source.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ModuleCupDerivedClassComparison | D2 | restored assigned module |

There are no current source importers or references to the absent module in the checkout.
The original downstream evaluation module can use the restored unchanged interface when its
own restoration is delivered. No downstream source adaptation is needed for this delivery.

## Verification of the returned failures

The repair session recompiled the restored comparison (29.6 seconds) and an exact scratch
copy of the current `ModuleCupDerivedHomologyTensor` (10.6 seconds). Both compile cleanly.
The latter is deliberately excluded from the delivery, preserving all its current public
operations and the completed tensor existence theorem. The former duplicate-instance error
is resolved by the published explicit `moduleCupTargetSymmetric` instance name. No consumer
adaptation is forced, and there is no change to the former comparison interface.

## Status

landed 20261014T020507-L-3810095 2026-10-14 (merge of deliver/D2/Sheaf.Paper.ModuleCupDerivedClassComparison)
