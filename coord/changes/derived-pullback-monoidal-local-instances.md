# AlgebraicGeometry.IsDerivedPullbackMonoidalModel: shared named instances

## Reason

Repair of reviewer X-d0021, return 8. The prior target reproducibly exceeded the
60-second limit. The predicate independently rebuilt the sheaf and derived instances,
while the descent statement used named wrappers for those same instances. Comparing
these large expressions in the assembled proof was expensive.

Use the descent module's already defined wrappers in the predicate's local instance
assignments, and register all those instances locally before elaborating the predicate.
The wrappers contain no holes or arbitrary chosen data: their bodies are exactly the
original expressions, or the original typeclass construction. Remove the theorem-scoped
transparency overrides and the duplicate registrations before the theorem. Neither the
file timeout nor the mathematical proof decomposition is changed.

The descent import is now `public import`: these fully defined wrappers occur in a
public definition body, so the module system requires a public import. The coherence
lemma remains a proof-only import. Existing signatures and declaration visibility stay
identical, and no new global instance registration is exported.

The original and revised predicates were checked by a scratch theorem proving their
equality by `rfl` (50.5 seconds); its source is retained in
`scratchpad/equality/lean/Sheaf/AlgebraicGeometry/ModelEquality.lean`.
The definition's meaning, including the chosen localization comparison maps, is unchanged
by definitional equality. The target compiled in 35.8 seconds in the full delivered set.
Both unchanged direct importers compiled against that output: PerfectRHomTensorComparison
in 33.3 seconds and PerfectTensorHomDuality in 8.7 seconds. No target statement-meaning
review is reopened by this definitionally equal implementation change.

## Old

The original definition, verbatim:

```lean
def IsDerivedPullbackMonoidalModel {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (m : (derivedPullback g).CoreMonoidal) : Prop := by
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.monoidalCategory T.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  letI := SheafOfModules.symmetricCategory T.sheaf
  haveI := Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  haveI := Classical.choice (SheafOfModules.tensorClosed T.sheaf).1
  letI := Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  letI := Classical.choice (SheafOfModules.tensorClosed T.sheaf).2.1
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings T.toRingedSpace)
  haveI := schemeModule_hasFunctorialFlatResolution X
  haveI := schemeModule_hasFunctorialFlatResolution T
  haveI := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))
  haveI := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
  letI := m.toMonoidal
  exact ∃ (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (_ : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    (_ : F.Additive) (mF : F.CoreMonoidal),
    (∀ M N, (mF.μIso M N).inv = eqToHom (hF _) ≫
      ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) M N).hom ≫
      (eqToHom (hF M).symm ⊗ₘ eqToHom (hF N).symm)) ∧
    ∃ ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh,
      (derivedPullback g).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)) ∧
      ∃ φ : ∀ P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _),
        (∀ P N p q n (h : p + q = n),
          F.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor _)
              (ComplexShape.up ℤ) p q n h) ≫ (φ P N).hom.f n =
            (mF.μIso (P.X p) (N.X q)).inv ≫
              HomologicalComplex.ιMapBifunctor
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
                (curriedTensor _) (ComplexShape.up ℤ) p q n h) ∧
        ∀ P N : CochainComplex
            (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlat (R := X.sheaf) P →
          CochainComplex.IsKFlat (R := X.sheaf) N →
          (m.μIso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)).hom ≫
              (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Q.map (φ P N).hom =
            (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ⊗ₘ
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
```

The returned delivery additionally imported the descent module privately, registered only
`pullbackDescentQLax` before this predicate, then registered the other wrappers and set
both backward transparency options to true before the existence theorem.

## New

Imports added to the original module:

```lean
import Sheaf.AlgebraicGeometry.ModulePullbackTensorCoherence
public import Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent
```

Local registrations before the predicate:

```lean
attribute [local instance] pullbackDescentModuleTensor moduleSymmetric modulePreadditive
  moduleClosed moduleGrothendieck moduleResolutions moduleDerivedMonoidal pullbackDescentQLax
```

The definition, with its signature unchanged:

```lean
def IsDerivedPullbackMonoidalModel {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (m : (derivedPullback g).CoreMonoidal) : Prop := by
  letI := pullbackDescentModuleTensor X
  letI := pullbackDescentModuleTensor T
  letI := moduleSymmetric X
  letI := moduleSymmetric T
  haveI := modulePreadditive X
  haveI := modulePreadditive T
  letI := moduleClosed X
  letI := moduleClosed T
  haveI := moduleGrothendieck X
  haveI := moduleGrothendieck T
  haveI := moduleResolutions X
  haveI := moduleResolutions T
  haveI := moduleDerivedMonoidal X
  haveI := moduleDerivedMonoidal T
  letI := m.toMonoidal
  exact ∃ (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (_ : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    (_ : F.Additive) (mF : F.CoreMonoidal),
    (∀ M N, (mF.μIso M N).inv = eqToHom (hF _) ≫
      ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) M N).hom ≫
      (eqToHom (hF M).symm ⊗ₘ eqToHom (hF N).symm)) ∧
    ∃ ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh,
      (derivedPullback g).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)) ∧
      ∃ φ : ∀ P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _),
        (∀ P N p q n (h : p + q = n),
          F.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor _)
              (ComplexShape.up ℤ) p q n h) ≫ (φ P N).hom.f n =
            (mF.μIso (P.X p) (N.X q)).inv ≫
              HomologicalComplex.ιMapBifunctor
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
                (curriedTensor _) (ComplexShape.up ℤ) p q n h) ∧
        ∀ P N : CochainComplex
            (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlat (R := X.sheaf) P →
          CochainComplex.IsKFlat (R := X.sheaf) N →
          (m.μIso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)).hom ≫
              (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Q.map (φ P N).hom =
            (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ⊗ₘ
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
```

The existence theorem retains its original signature and the complete assembly proof.
Its private categorical reassociation helper is fully proved. No theorem-scoped
transparency override remains, and no additional declarations or holes are introduced
by this repair.

## Users

`tools/downstream.py --uses IsDerivedPullbackMonoidalModel` reports two textual users:
the item and `PerfectRHomTensorComparison`. There are 349 transitive downstream modules;
all receive a definitionally equal predicate. The two direct importers requested by the
reviewer are tested unchanged against the repaired compiled target. No adaptations are
included in the delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel | C2 | Same predicate; faster assembly elaboration. |
| Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison | unclaimed in the local snapshot | Definitionally equal predicate; unchanged source compiled against the repair. |
| Sheaf.AlgebraicGeometry.PerfectTensorHomDuality | unclaimed in the local snapshot | Unchanged existence-theorem signature; unchanged source compiled against the repair. |

## Status

landed 20261012T163612-L-2784419 2026-10-12 (merge of deliver/C2/Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel)
