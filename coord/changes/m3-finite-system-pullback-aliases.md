# WeilConjectures.finiteSystemRings and finite-system operation aliases

## Reason

The finite-system proof repeatedly compares its operations with the existing
`AlgebraicGeometry.ProEtale.VaryingRing` operations at the lifted coefficient tower
`R n = CommRingCat.of (ULift (A n))`. Expanding both independent presentations
made Lean spend tens of thousands of heartbeats comparing the same ringed
sequence-site structures. The delivery makes those specializations explicit.

Changed bodies, all in the assigned module:

- `finiteSystemRings` and `finiteSystemRingTransition` now call
  `VaryingRing.coefficients` and `VaryingRing.coefficientTransition`.
- `finiteSystems`, `finiteSystemDerived`, `finiteSystemEvaluation`,
  `finiteSystemPushforward`, `finiteSystemPullback` and `finiteSystemAdjunction`
  call the corresponding varying-ring operation with that lifted tower.
- `finiteSystemDerivedEvaluation` explicitly calls `mapDerivedCategory` on
  `finiteSystemEvaluation`, which is the construction denoted by the original
  `SemilinearSections.e` expression. Its coefficient-level abelian and derived
  structures are explicitly the ones already used by the canonical constant-ring
  derived operations. `finiteSystemDerivedPullbackEvaluation` likewise fixes
  those two existing structures locally before constructing its localization
  square. This avoids kernel comparisons between separately inferred
  `SemilinearSections.moduleAbelian` and `SheafOfModules.instAbelian` terms.
- A local instance priority selects `SemilinearSections.hasDerived` for system
  derived functors. This is the localization explicitly used by `DS` and
  `VaryingRing.Derived`; it avoids a competing projection-restriction instance.
- `finiteSystemPullbackEvaluation` and `finiteSystemModuleComposition` have
  explicit result types spelling the same functors as their defining choice
  theorems. Their chosen values are unchanged.

These are the same constant sheaves, lifted transition homomorphisms, categories
of modules on the ringed sequence site, direct image functor, chosen left adjoint,
adjunction and exact evaluation functor as before. No arbitrary existence witness is newly
chosen and no mathematical statement changes. The chosen left adjoint and its
adjunction come from the same right-adjoint proposition. The varying-ring import
is now public because the definition bodies refer to it.


## Old

```lean
abbrev finiteSystemRings (X : Scheme.{u}) (n : ℕ) :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  proEtaleConstantRing.{u} X (A n)
```

```lean
def finiteSystemRingTransition (X : Scheme.{u}) (n : ℕ) :
    finiteSystemRings.{u} A X (n + 1) ⟶ finiteSystemRings.{u} A X n :=
  (constantSheaf.{u, u + 1, u + 1, u + 2}
    (ProEt.topology X) CommRingCat.{u + 1}).map
    (X := CommRingCat.of (ULift.{u + 1, u} (A (n + 1))))
    (Y := CommRingCat.of (ULift.{u + 1, u} (A n)))
    (CommRingCat.ofHom ((τ n).hom.ulift))
```

```lean
abbrev finiteSystems (X : Scheme.{u}) :=
  Systems.{u + 1, u, u + 1} (ProEt.topology X) (finiteSystemRings.{u} A X)
    (finiteSystemRingTransition.{u} A τ X)
```

```lean
abbrev finiteSystemDerived (X : Scheme.{u}) :=
  DS.{u + 1, u, u + 1} (ProEt.topology X) (finiteSystemRings.{u} A X)
    (finiteSystemRingTransition.{u} A τ X)
```

```lean
abbrev finiteSystemEvaluation (X : Scheme.{u}) (n : ℕ) :=
  SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology X) (finiteSystemRings.{u} A X)
    (finiteSystemRingTransition.{u} A τ X) n
```

```lean
abbrev finiteSystemPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteSystems.{u} A τ X ⥤ finiteSystems.{u} A τ Y :=
  SheafOfModules.pushforward.{u + 1} (F := finiteSystemBaseChange.{u} f)
    (J := coefficientSequenceTopology (ProEt.topology Y))
    (K := coefficientSequenceTopology (ProEt.topology X))
    (S := ring.{u + 1, u, u + 1} _ (systemRing.{u + 1, u, u + 1} (ProEt.topology Y)
      (finiteSystemRings.{u} A Y)
      (finiteSystemRingTransition.{u} A τ Y)))
    (R := ring.{u + 1, u, u + 1} _ (systemRing.{u + 1, u, u + 1} (ProEt.topology X)
      (finiteSystemRings.{u} A X)
      (finiteSystemRingTransition.{u} A τ X)))
    ⟨Functor.whiskerRight (finiteSystemRingMap.{u} A τ f).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
```

```lean
abbrev finiteSystemPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (finiteSystemPushforward.{u} A τ f).leftAdjoint
```

```lean
abbrev finiteSystemAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Adjunction.ofIsRightAdjoint (finiteSystemPushforward.{u} A τ f)
```

```lean
abbrev finiteSystemDerivedEvaluation (X : Scheme.{u}) (n : ℕ) :=
  e.{u + 1, u, u + 1} (ProEt.topology X) (finiteSystemRings.{u} A X)
    (finiteSystemRingTransition.{u} A τ X) n
```

```lean
def finiteSystemPullbackEvaluation [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (finiteSystemPullbackEvaluation_existsUnique.{u} A τ f n).exists.choose
```

```lean
def finiteSystemDerivedPullbackEvaluation [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    finiteSystemDerivedPullback.{u} A τ f ⋙ finiteSystemDerivedEvaluation.{u} A τ X n ≅
      finiteSystemDerivedEvaluation.{u} A τ Y n ⋙ proEtaleConstantRingDerivedPullback (A n) f :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (finiteSystemPullbackEvaluation.{u} A τ f n) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
```

```lean
def finiteSystemModuleComposition [∀ n, Finite (A n)]
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (n : ℕ) :=
  (proEtaleConstantRingModulePullbackComposition h k (A n)).choose
```

## New

```lean
abbrev finiteSystemRings (X : Scheme.{u}) (n : ℕ) :
    Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  AlgebraicGeometry.ProEtale.VaryingRing.coefficients
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n))) X n
```

```lean
def finiteSystemRingTransition (X : Scheme.{u}) (n : ℕ) :
    finiteSystemRings.{u} A X (n + 1) ⟶ finiteSystemRings.{u} A X n :=
  AlgebraicGeometry.ProEtale.VaryingRing.coefficientTransition
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n)))
    (fun n ↦ CommRingCat.ofHom ((τ n).hom.ulift)) X n
```

```lean
abbrev finiteSystems (X : Scheme.{u}) :=
  AlgebraicGeometry.ProEtale.VaryingRing.Modules
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n)))
    (fun n ↦ CommRingCat.ofHom ((τ n).hom.ulift)) X
```

```lean
abbrev finiteSystemDerived (X : Scheme.{u}) :=
  AlgebraicGeometry.ProEtale.VaryingRing.Derived
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n)))
    (fun n ↦ CommRingCat.ofHom ((τ n).hom.ulift)) X
```

```lean
abbrev finiteSystemEvaluation (X : Scheme.{u}) (n : ℕ) :
    finiteSystems A τ X ⥤ proEtaleRingModules X (proEtaleConstantRing X (A n)) :=
  AlgebraicGeometry.ProEtale.VaryingRing.eval
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n)))
    (fun n ↦ CommRingCat.ofHom ((τ n).hom.ulift)) X n
```

```lean
abbrev finiteSystemPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteSystems.{u} A τ X ⥤ finiteSystems.{u} A τ Y :=
  AlgebraicGeometry.ProEtale.VaryingRing.push
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n)))
    (fun n ↦ CommRingCat.ofHom ((τ n).hom.ulift)) f
```

```lean
abbrev finiteSystemPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  AlgebraicGeometry.ProEtale.VaryingRing.pull
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n)))
    (fun n ↦ CommRingCat.ofHom ((τ n).hom.ulift)) f
```

```lean
abbrev finiteSystemAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteSystemPullback A τ f ⊣ finiteSystemPushforward A τ f :=
  AlgebraicGeometry.ProEtale.VaryingRing.moduleAdj
    (fun n ↦ CommRingCat.of (ULift.{u + 1, u} (A n)))
    (fun n ↦ CommRingCat.ofHom ((τ n).hom.ulift)) f
```

```lean
abbrev finiteSystemDerivedEvaluation (X : Scheme.{u}) (n : ℕ) :
    finiteSystemDerived.{u} A τ X ⥤ proEtaleDerivedCategory.{u} X (A n) :=
  @CategoryTheory.Functor.mapDerivedCategory (finiteSystems.{u} A τ X) _ _ _
    (proEtaleRingModules.{u} X (proEtaleConstantRing.{u} X (A n))) _
    (@SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} X.ProEt _ (ProEt.topology X)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing.{u} X (A n)))
      (GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} X)
      (SemilinearSections.locallyBijective.{u + 1, u, u + 1} (ProEt.topology X)))
    (proEtaleRingModules_hasDerivedCategory.{u} X (proEtaleConstantRing.{u} X (A n)))
    (finiteSystemEvaluation.{u} A τ X n) _ _ _
```

```lean
def finiteSystemPullbackEvaluation [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    finiteSystemPullback.{u} A τ f ⋙ finiteSystemEvaluation.{u} A τ X n ≅
      finiteSystemEvaluation.{u} A τ Y n ⋙ proEtaleConstantRingPullback (A n) f :=
  (finiteSystemPullbackEvaluation_existsUnique.{u} A τ f n).exists.choose
```

```lean
def finiteSystemDerivedPullbackEvaluation [∀ n, Finite (A n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    finiteSystemDerivedPullback.{u} A τ f ⋙ finiteSystemDerivedEvaluation.{u} A τ X n ≅
      finiteSystemDerivedEvaluation.{u} A τ Y n ⋙ proEtaleConstantRingDerivedPullback (A n) f := by
  letI : Abelian (proEtaleRingModules.{u} X (proEtaleConstantRing.{u} X (A n))) :=
    @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} X.ProEt _ (ProEt.topology X)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing.{u} X (A n)))
      (GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} X)
      (SemilinearSections.locallyBijective.{u + 1, u, u + 1} (ProEt.topology X))
  letI : Abelian (proEtaleRingModules.{u} Y (proEtaleConstantRing.{u} Y (A n))) :=
    @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} Y.ProEt _ (ProEt.topology Y)
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing.{u} Y (A n)))
      (GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat.{u + 1} Y)
      (SemilinearSections.locallyBijective.{u + 1, u, u + 1} (ProEt.topology Y))
  letI : HasDerivedCategory (proEtaleRingModules.{u} X (proEtaleConstantRing.{u} X (A n))) :=
    proEtaleRingModules_hasDerivedCategory.{u} X (proEtaleConstantRing.{u} X (A n))
  letI : HasDerivedCategory (proEtaleRingModules.{u} Y (proEtaleConstantRing.{u} Y (A n))) :=
    proEtaleRingModules_hasDerivedCategory.{u} Y (proEtaleConstantRing.{u} Y (A n))
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (finiteSystemPullbackEvaluation.{u} A τ f n) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
```

```lean
def finiteSystemModuleComposition [∀ n, Finite (A n)]
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (n : ℕ) :
    proEtaleConstantRingPullback (A n) (h ≫ k) ≅
      proEtaleConstantRingPullback (A n) k ⋙ proEtaleConstantRingPullback (A n) h :=
  (proEtaleConstantRingModulePullbackComposition h k (A n)).choose
```

The following local priority makes the elaborated derived system functors use
exactly the instance fixed by `DS` and `VaryingRing.Derived`:

```lean
attribute [local instance 3000] SemilinearSections.hasDerived
```

The coefficient structures in the explicit expressions above are those of
`proEtaleConstantRingDerivedPullback`. Universe arguments are explicit to prevent
ambiguous inference through maximum universe levels. The varying-ring import
is public because the transparent bodies refer to it.

## Users

The downstream search found 511 modules; only these modules mention the changed
names. The table lists every direct name consumer reported by `--uses`.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.FiniteSystemPullbackCoherence` | M3 | Assigned module; equivalent operation aliases and complete proofs. |
| `Sheaf.Paper.IntegralPullbackComposition` | unclaimed | Compile unchanged against the new definitions. |
| `Sheaf.Paper.IntegralSystemReductionFullyFaithful` | unclaimed | Compile unchanged against the new definitions. |
| `Sheaf.Paper.IntegralSystemPullbackLiftAssociativity` | unclaimed | Compile unchanged against the new definitions. |
| `Sheaf.Paper.IntegralPullbackSystemComparison` | unclaimed | Compile unchanged against the new definitions. |

No target signature changes. The maintainer should include these definition
aliases and the explicit category structures in the target meaning review.
Validation results are recorded in `report.md`.

## Status

landed 20261020T221247-L-4165169 2026-10-20 (merge of deliver/M3/Sheaf.Paper.FiniteSystemPullbackCoherence)
