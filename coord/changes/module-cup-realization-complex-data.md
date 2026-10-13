# AlgebraicGeometry.Scheme.Modules.CupResolutionPairing.derivedMap

## Reason
Move the existing integer-complex, realization and localized-map constructions verbatim
into `Sheaf.Paper.ModuleCupRealizationComplexData`, publicly reexported by the original
module. This breaks the import cycle that would result if the new standalone existence
and augmentation-compatibility modules imported their consumer. No existing mathematical
signature or body changes; no data is chosen from the new existence theorem.

## Old
In `Sheaf.Paper.ModuleCupResolutionRealization`:
```lean
/-- Extend a nonnegative resolution to integer degrees by zero. -/
abbrev CupAcyclicResolution.integerComplex {F : X.Modules} (D : CupAcyclicResolution F) :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ :=
  D.K.extend ComplexShape.embeddingUpNat

/-- The localized augmentation, with the extended single complex identified with F[0]. -/
def CupAcyclicResolution.derivedAugmentation {F : X.Modules} (D : CupAcyclicResolution F) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ⟶
      DerivedCategory.Q.obj D.integerComplex :=
  DerivedCategory.Q.map
    ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).inv ≫
      HomologicalComplex.extendMap D.augmentation ComplexShape.embeddingUpNat)

/-- An augmentation is inverted by the derived localization. -/
instance CupAcyclicResolution.derivedAugmentation_isIso
    {F : X.Modules} (D : CupAcyclicResolution F) : IsIso D.derivedAugmentation := by
  let : QuasiIso D.augmentation := D.quasiIso
  unfold CupAcyclicResolution.derivedAugmentation
  rw [Functor.map_comp]
  infer_instance

/-- The section formula for the cochain morphism realizing the bilinear pairing.
It specifies all nonzero tensor summands; extension by zero supplies the others. -/
def CupResolutionPairing.Realizes {F G : X.Modules} (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex) : Prop :=
  ∀ (p q : ℕ) (V : X.Opens) (a : Γ(D.left.K.X p, V)) (b : Γ(D.right.K.X q, V)),
    ((HomologicalComplex.ιTensorObj D.left.integerComplex D.right.integerComplex
        (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ) (by omega) ≫ t.f (p + q) ≫
      (D.target.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom).val.app (op V)
        (tmulSection
          ((D.left.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) a)
          ((D.right.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) b)))
      = D.pair p q V a b

/-- The derived morphism attached to a cochain realization. This is an explicit
composite of localized augmentations and the canonical tensor comparison. -/
def CupResolutionPairing.derivedMap {F G : X.Modules} (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ⊗
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj (F ⊗ G)) :=
  (D.left.derivedAugmentation ⊗ₘ D.right.derivedAugmentation) ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q D.left.integerComplex D.right.integerComplex ≫
    DerivedCategory.Q.map t ≫ inv D.target.derivedAugmentation

```

## New
The same declarations and bodies, verbatim, in
`Sheaf.Paper.ModuleCupRealizationComplexData`, with the same local instances;
`ModuleCupResolutionRealization` publicly imports that module.
The canonical single-tensor comparison import remains directly public in the original
module, and is public in the augmentation theorem module whose statement uses it.
The extracted data module does not use or import this comparison.
The old theorem signature is unchanged. All downstream uses retain the same definitions
and meaning. No target statement changes and no adaptation of another existing module
is needed.

```lean
/-- Extend a nonnegative resolution to integer degrees by zero. -/
abbrev CupAcyclicResolution.integerComplex {F : X.Modules} (D : CupAcyclicResolution F) :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ :=
  D.K.extend ComplexShape.embeddingUpNat

/-- The localized augmentation, with the extended single complex identified with F[0]. -/
def CupAcyclicResolution.derivedAugmentation {F : X.Modules} (D : CupAcyclicResolution F) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ⟶
      DerivedCategory.Q.obj D.integerComplex :=
  DerivedCategory.Q.map
    ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).inv ≫
      HomologicalComplex.extendMap D.augmentation ComplexShape.embeddingUpNat)

/-- An augmentation is inverted by the derived localization. -/
instance CupAcyclicResolution.derivedAugmentation_isIso
    {F : X.Modules} (D : CupAcyclicResolution F) : IsIso D.derivedAugmentation := by
  let : QuasiIso D.augmentation := D.quasiIso
  unfold CupAcyclicResolution.derivedAugmentation
  rw [Functor.map_comp]
  infer_instance

/-- The section formula for the cochain morphism realizing the bilinear pairing.
It specifies all nonzero tensor summands; extension by zero supplies the others. -/
def CupResolutionPairing.Realizes {F G : X.Modules} (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex) : Prop :=
  ∀ (p q : ℕ) (V : X.Opens) (a : Γ(D.left.K.X p, V)) (b : Γ(D.right.K.X q, V)),
    ((HomologicalComplex.ιTensorObj D.left.integerComplex D.right.integerComplex
        (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ) (by omega) ≫ t.f (p + q) ≫
      (D.target.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom).val.app (op V)
        (tmulSection
          ((D.left.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) a)
          ((D.right.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op V) b)))
      = D.pair p q V a b

/-- The derived morphism attached to a cochain realization. This is an explicit
composite of localized augmentations and the canonical tensor comparison. -/
def CupResolutionPairing.derivedMap {F G : X.Modules} (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ⊗
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj (F ⊗ G)) :=
  (D.left.derivedAugmentation ⊗ₘ D.right.derivedAugmentation) ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q D.left.integerComplex D.right.integerComplex ≫
    DerivedCategory.Q.map t ≫ inv D.target.derivedAugmentation

```

## Users
| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModuleCupResolutionRealization | A2 | definitions publicly reexported; proof changed |
| Sheaf.Paper.ModuleCupRealizationComplexData | A2 | new home of unchanged constructions |
| Sheaf.Paper.ModuleCupResolutionExistence | A2 | new consumer of constructions |
| Sheaf.Paper.ModuleCupResolutionAugmentation | A2 | new consumer of constructions |
| Sheaf.Paper.ModuleCupRealizationEvaluation | unclaimed in local snapshot | same public definitions |
| Sheaf.Paper.ModuleCupResolutionInvariance | unclaimed in local snapshot | same public definitions |
| Sheaf.Paper.ModuleCupEqualDerivedMapsClass | unclaimed in local snapshot | same public definitions |

## Status
landed 20261013T143543-L-559734 2026-10-13 (merge of deliver/A2/Sheaf.Paper.ModuleCupResolutionRealization)
