# CondensedTateRealization canonical constructions and elaboration

## Reason

The original definitions repeatedly expand completed coefficients and infer distinct
presentations of the same derived-category and tensor structures. Diagnostic runs
exceeded the 60-second limit. The retained construction aliases and local elaboration
controls reduce the final single-file compile to 57.9 seconds.

## Old

```lean
instance liftedQNormedField : NormedField (LiftedQ.{u} l) :=
  NormedField.induced (ULift.{u} ℚ_[l]) ℚ_[l]
    (ULift.ringEquiv : ULift.{u} ℚ_[l] ≃+* ℚ_[l]).toRingHom ULift.down_injective
```

```lean
instance liftedQNormedAlgebra : NormedAlgebra ℚ_[l] (LiftedQ.{u} l) where
  toAlgebra := inferInstanceAs (Algebra ℚ_[l] (ULift.{u} ℚ_[l]))
  norm_smul_le a x := norm_smul_le a x.down
```

```lean
abbrev CompletedRing : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  pbcAdicCompletion X (pbcIntegralDatum l (LiftedQ.{u} l))
```

```lean
def rationalToQbar :=
  coefficientMap
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (rationalDownRingMap l ≫
          Profinite.padicCondensedRingToPadicSubfieldCondensedRing l
          (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ≫
            Profinite.padicSubfieldCondensedRingToPadicAlgCl l ⟨⊥, inferInstance⟩)) X
```

```lean
def derivedAugmentation (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    (DerivedCategory.singleFunctor _ 0).obj
      ((integralEncoding X l r).functor.obj (integralPower X l d)) ⟶
        reconstructed X l r d :=
  (limitAdjunction X l).homEquiv _ _
    (((Functor.const ℕᵒᵖ).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor _ 0).map (augmentation X l r d))
```

```lean
abbrev ambientRealization (r : At l (LiftedQ.{u} l) X) :=
  pbcDerivedExtend (scalarMap X l r) ⋙
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.inverse ⋙
      (Mod.extendScalars (rationalToQbar X l)).leftDerivedFunctor
```

```lean
def realized (r : At l (LiftedQ.{u} l) X) (M : Integral l (LiftedQ.{u} l) X) :=
  (Mod.extendScalars (rationalToQbar X l)).leftDerivedFunctor.obj
    (r.realization.functor.obj (ScalarLocalization.mk M)).obj
```

```lean
def realizationComparison (r : At l (LiftedQ.{u} l) X) (M : Integral l (LiftedQ.{u} l) X) :
    (ambientRealization X l r).obj M.obj ≅ realized X l r M :=
  (Mod.extendScalars (rationalToQbar X l)).leftDerivedFunctor.mapIso
    (((moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.inverse.mapIso
        (r.scalarExtension.app M).symm) ≪≫
      (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.unitIso.symm.app _)
```

```lean
noncomputable instance ambientRealizationCommShift (r : At l (LiftedQ.{u} l) X) :
    (ambientRealization X l r).CommShift ℤ := by
  letI : (pbcDerivedRestrict (scalarMap X l r)).CommShift ℤ :=
    inferInstanceAs ((pbcRestrict (scalarMap X l r)).mapDerivedCategory.CommShift ℤ)
  letI : (pbcDerivedExtend (scalarMap X l r)).CommShift ℤ :=
    (pbcDerivedScalarAdjunction (scalarMap X l r)).leftAdjointCommShift ℤ
  letI : PreservesFiniteLimits (Mod.extendScalars (rationalToQbar X l)) :=
    rationalToQbar_preservesFiniteLimits X l
  letI : (Mod.extendScalars (rationalToQbar X l)).leftDerivedFunctor.CommShift ℤ := by
    exact Functor.CommShift.ofIso
      ((Mod.extendScalars (rationalToQbar X l)).leftDerivedFunctorIsoMapDerivedCategory.symm) ℤ
  unfold ambientRealization
  infer_instance
```

## New

```lean
instance liftedQNormedField : NormedField (LiftedQ.{u} l) :=
  fast_instance% NormedField.induced (ULift.{u} ℚ_[l]) ℚ_[l]
    (ULift.ringEquiv : ULift.{u} ℚ_[l] ≃+* ℚ_[l]).toRingHom ULift.down_injective
```

```lean
instance liftedQNormedAlgebra : NormedAlgebra ℚ_[l] (LiftedQ.{u} l) := inferInstance
```

```lean
def CompletedRing : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  pbcAdicCompletion X (pbcIntegralDatum l (LiftedQ.{u} l))
```

```lean
def rationalToQbar : Coefficient (LiftedQ.{u} l) X ⟶
    condensedRingObj (Profinite.padicAlgClRingObj l) X :=
  coefficientMap
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (rationalDownRingMap l ≫
          Profinite.padicCondensedRingToPadicSubfieldCondensedRing l
          (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ≫
            Profinite.padicSubfieldCondensedRingToPadicAlgCl l ⟨⊥, inferInstance⟩)) X
```

```lean
def derivedAugmentation (r : At l (LiftedQ.{u} l) X) (d : ℕ) :=
  let A := pbcModules X (CompletedRing X l)
  let D := reductionTowerCategory X (reductionModuleRing X (CompletedRing X l))
  let F : A ⥤ D := Functor.const ℕᵒᵖ
  let S : A ⥤ DerivedCategory A := DerivedCategory.singleFunctor A 0
  let V : D ⥤ DerivedCategory D := DerivedCategory.singleFunctor D 0
  let M : A := (integralEncoding X l r).functor.obj (integralPower X l d)
  let N : D := encodedTower X l r d
  let f : F.obj M ⟶ N := augmentation X l r d
  (limitAdjunction X l).homEquiv (S.obj M) (V.obj N)
    ((F.mapDerivedCategorySingleFunctor 0).hom.app M ≫ V.map f)
```

```lean
abbrev ambientRealization (r : At l (LiftedQ.{u} l) X) :=
  pbcDerivedExtend (scalarMap X l r) ⋙
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.inverse ⋙
      (rationalDerivedExtension X l)
```

```lean
def realized (r : At l (LiftedQ.{u} l) X) (M : Integral l (LiftedQ.{u} l) X) :=
  (rationalDerivedExtension X l).obj
    (r.realization.functor.obj (ScalarLocalization.mk M)).obj
```

```lean
def realizationComparison (r : At l (LiftedQ.{u} l) X) (M : Integral l (LiftedQ.{u} l) X) :
    (ambientRealization X l r).obj M.obj ≅ realized X l r M :=
  (rationalDerivedExtension X l).mapIso
    (((moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.inverse.mapIso
        (r.scalarExtension.app M).symm) ≪≫
      (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.unitIso.symm.app _)
```

```lean
noncomputable instance ambientRealizationCommShift (r : At l (LiftedQ.{u} l) X) :
    (ambientRealization X l r).CommShift ℤ := by
  letI : (pbcDerivedRestrict (scalarMap X l r)).CommShift ℤ :=
    inferInstanceAs ((pbcRestrict (scalarMap X l r)).mapDerivedCategory.CommShift ℤ)
  letI : (pbcDerivedExtend (scalarMap X l r)).CommShift ℤ :=
    (pbcDerivedScalarAdjunction (scalarMap X l r)).leftAdjointCommShift ℤ
  let G : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) ⥤
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (Coefficient (LiftedQ.{u} l) X) :=
    Mod.comap (rationalToQbar X l)
  letI : G.mapDerivedCategory.CommShift ℤ := inferInstance
  letI : (rationalDerivedExtension X l).CommShift ℤ := by
    unfold rationalDerivedExtension
    exact (Mod.derivedExtendMapDerivedCategoryAdjunction
      (rationalToQbar X l)).leftAdjointCommShift ℤ
  unfold ambientRealization
  infer_instance
```

```lean
def rationalDerivedExtension :=
  let A := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (Coefficient (LiftedQ.{u} l) X)
  let B := Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj l) X)
  let F : A ⥤ B := Mod.extendScalars (rationalToQbar X l)
  F.leftDerivedFunctor
```

The lifted normed field is Mathlib fast_instance% normalization of the same induced
structure. Its algebra is the canonical ULift normed algebra with identical scalar
operations. CompletedRing retains its exact completion body as a regular definition.
The explicit rationalToQbar signature records its previously inferred endpoints.

Derived augmentation remains the same adjunction transpose of the actual cone;
local functors pin its category instances. rationalDerivedExtension names the actual
left derived extension once; consumers reuse it. The shift is the canonical shift
on the left adjoint of exact derived restriction. Adjunction compatibility determines
this shift and identifies it with the original exact scalar-extension comparison.
The actual Tate objects, coefficient maps, units, counits and projection equations
are unchanged. No target statement or target interpretation is weakened.

The following controls are local and do not export attributes: strict backward
transparency with scoped relaxation, irreducibility of generic derived constructions,
reducibility of the three standard derived-category instance aliases, their instance
priority, and disabling generic essentially-small sheafification at each declaration.
The alias reducibility setting matches CondensedERealizationDefinitions; it changes
elaboration transparency, not kernel checking or the trust basis. Standard style
linting is disabled while elaboration and kernel checks remain active.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedTateRealization | C9 | Same canonical constructions, named derived extension, local elaboration controls. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | Direct importer; uses none of the changed declarations; compiles unchanged (reviewer, 2026-10-26). |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | Direct importer; uses none of the changed declarations; compiles unchanged (reviewer, 2026-10-26). |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed | Direct importer; uses none of the changed declarations; compiles unchanged (reviewer, 2026-10-26). |

The three direct Lean importers above (landed 2026-10-25/26) import the module
publicly but name none of the changed declarations; each compiles unchanged against
the delivered module, so none requires adaptation. The unfinished DAG
parents and blueprint unit remain attached and needed. No withdrawal is proposed.
There is no forced adaptation and no source-library edit.

## Status

landed 20261025T205903-L-3389861 2026-10-25 (merge of deliver/C9/Sheaf.Paper.CondensedTateRealization)
