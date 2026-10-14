# AlgebraicGeometry.Scheme.Modules.exists_cupDerivedClassComparison

## Reason

Repair the landed delivery at tip 515b3096579d5cc94808005b5a6c390476ab90ca.
Its public import of `ModuleCupNaiveDerivedCompatibility` introduces generated local
instance names also exported by `GlobalTensorPullbackMonoidalNormalization`. These
modules collide in the combined environment used by the global axiom/sorry probe.
The original comparison compiles alone, so that check did not establish global compatibility.

The comparison uses no cup compatibility theorem: it needs only the definition
`moduleCup_globalComparison X K`, whose body is exactly
`(moduleCup_comparisonNatTrans X).app K`. Unfold that wrapper at every use and import
`ModuleCupKInjectiveTarget`, which defines the natural transformation, directly.

## Old

```lean
public import Sheaf.Paper.ModuleCupNaiveDerivedCompatibility
```

Public interface at the broken tip:

```lean
/-- Derived global sections of a coefficient sheaf placed in degree zero. -/
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

## New

```lean
public import Sheaf.Paper.ModuleCupKInjectiveTarget
```

Public interface after unfolding the wrapper:

```lean
/-- Derived global sections of a coefficient sheaf placed in degree zero. -/
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
          ((moduleCup_comparisonNatTrans X).app D.integerComplex ≫
            (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
              (inv D.derivedAugmentation))
          (cupLocalizedCycleClass K n z)


theorem exists_cupDerivedClassComparison : Nonempty (CupDerivedClassComparison X)
```

All universes, binders, declaration names and visibility stay the same. The abbreviation
`cupDerivedSections` is unchanged. In `CupDerivedClassComparison.on_cycles`, the sole
replacement is definitionally equal by the original wrapper's defining equation. The
existence theorem's signature is textually unchanged. Every existing Lean docstring is
unchanged. The injective-resolution construction, isomorphisms, transport and cycle lift
are preserved; only the spelling of the comparison component and its unfolding change.
No new declaration, axiom or sorry is introduced.

The DAG's proof and proof dependencies record the direct natural-transformation component
and remove the unused naive/derived compatibility proof dependency. Its statement is retained.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ModuleCupDerivedClassComparison | XRa0a656f89c54729e (repair; original D2) | unfolds the comparison wrapper and removes the conflicting import |

A source search at the supplied snapshot finds no module importing this comparison and no
external reference to its three public declarations. No consumer adaptation is required.
No dependency module is edited. The compatibility module itself remains available to its
other users; this repair removes it from this comparison's dependency closure.

## Verification of the returned failures

Only `lcompile.py` single-file checks were used, with the unchanged 60-second limit and
remote fallback disabled. The landed source compiled alone in 29.0 seconds. Adding a
temporary direct import of `GlobalTensorPullbackMonoidalNormalization` reproduced the
collision in 1.3 seconds (the CommRing generated name, with the opposite import order).
The repaired comparison with the same temporary import compiled in 35.3 seconds.

The repaired source also compiled with temporary `import all` directives for each of its
three dependencies, exercising their private import environments, in 30.7 seconds.
The axiom output for `exists_cupDerivedClassComparison`, `cupDerivedSections` and
`CupDerivedClassComparison` was exactly `propext`, `Classical.choice`, `Quot.sound`.
The temporary imports and axiom-print commands were removed before the final check.
The final source compiled cleanly in 32.4 seconds, with no warnings or errors.
No .check file, second-reading evidence, server compile, build or delivery was produced.

## Status

landed 20261014T023930-L-13515 2026-10-14 (merge of deliver/XRa0a656f89c54729e/Sheaf.Paper.ModuleCupDerivedClassComparison)
