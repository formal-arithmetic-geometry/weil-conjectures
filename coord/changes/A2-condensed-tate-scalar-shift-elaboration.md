# AlgebraicGeometry.ProEtale.CondensedTateRealization.ambientRealizationCommShift

## Reason

Filling four existing proofs initially exceeded the 60-second single-file limit.
Profiling isolated repeated comparison of equivalent derived-category instance
wrappers and expansion of the scalar/shift constructions. Record the existing
coefficient, tower, reconstructed-object and derived scalar-functor types
explicitly; use the standard reductionDerivedCategory alias for the reconstructed
objects. Reuse the left functor already recorded by the existing concrete derived scalar
adjunction. This is the original leftDerivedFunctor, with its existing instance
arguments; the local helper returns its F parameter and makes no choice from an
existence statement. Elaborate the canonical shift first for a generic coefficient
map and then specialize.

The named tateRlim and tateRlimProjection interfaces are definitionally the existing
completedRlim and completedRlimProjection. The reconstructed object and limit
adjunction use that same functor. singleDerivedProjection composes a derived natural
transformation with the exact-functor single comparison, abstracting over the
abelian categories and exact functor. Specializing it gives exactly the original
reconstructedProjection formula. This removes repeated kernel expansion of the
concrete tower and module categories; it introduces no new mathematical choice.

The existing standard derived-category aliases remain locally reducible. Add the
tower alias to that list and its local priority, and prefer the reduction-module
alias locally so the explicit map types use the same standard localization as the
existing completed Rlim functor. Local opacity of upperStarFromPoint prevents
unrelated expansions. integralEncoding is locally opaque until augmentation
naturality needs its construction. No public attribute or import is changed, no
new transparency relaxation is introduced, and no target statement or mathematical
definition changes meaning. Lean's default asynchronous checking is retained. Explicit ambient-category
arguments in scalar operations, and explicit source and target functor types for
ambient and ordinary restriction, avoid inferring the same sheaf category repeatedly.

Target statements depending on these definitions are subject to the required
independent statement review; the formulas remain definitionally equal to their
original constructions. Final compilation and downstream verification are recorded
in report.md.

## Old

```lean
def integralEncoding (r : At l (LiftedQ.{u} l) X) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) (R X l)).trans
    (ringModuleEquivalenceOfIso X
      ((adicLisseForget X).mapIso (integralComparison X l r)).symm)
```

```lean
def encodedTower (r : At l (LiftedQ.{u} l) X) (d : ℕ) :=
  finiteTower X l d ⋙ (integralEncoding X l r).functor
```

```lean
def reconstructed (r : At l (LiftedQ.{u} l) X) (d : ℕ) :=
  (completedRlim X (CompletedRing X l)).obj
    ((DerivedCategory.singleFunctor _ 0).obj (encodedTower X l r d))
```

```lean
def shiftedReconstructed (r : At l (LiftedQ.{u} l) X) (d : ℕ) :=
  (shiftFunctor _ (2 * d : ℤ)).obj (reconstructed X l r d)
```

```lean
def limitAdjunction :
    (Functor.const ℕᵒᵖ :
      pbcModules X (CompletedRing X l) ⥤ _).mapDerivedCategory ⊣
      completedRlim X (CompletedRing X l) :=
  (constLimAdj : (Functor.const ℕᵒᵖ :
    pbcModules X (CompletedRing X l) ⥤ _) ⊣
      completedTowerLimit X (CompletedRing X l)).mapDerivedCategoryRightDerivedAdjunction
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
def scalarMap (r : At l (LiftedQ.{u} l) X) := r.integralIso.hom ≫ r.inclusion
```

```lean
def rationalDerivedExtension :=
  let A := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (Coefficient (LiftedQ.{u} l) X)
  let B := Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj l) X)
  let F : A ⥤ B := Mod.extendScalars (rationalToQbar X l)
  F.leftDerivedFunctor
```

```lean
abbrev ambientRealization (r : At l (LiftedQ.{u} l) X) :=
  pbcDerivedExtend (scalarMap X l r) ⋙
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.inverse ⋙
      (rationalDerivedExtension X l)
```

```lean
abbrev ambientRestriction (r : At l (LiftedQ.{u} l) X) :=
  (Mod.comap (rationalToQbar X l)).mapDerivedCategory ⋙
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.functor ⋙
      pbcDerivedRestrict (scalarMap X l r)
```

```lean
def scalarAdjunction (r : At l (LiftedQ.{u} l) X) :
    ambientRealization X l r ⊣ ambientRestriction X l r :=
  ((pbcDerivedScalarAdjunction (scalarMap X l r)).comp
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.symm.toAdjunction).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (rationalToQbar X l))
```

```lean
def realized (r : At l (LiftedQ.{u} l) X) (M : Integral l (LiftedQ.{u} l) X) :=
  (rationalDerivedExtension X l).obj
    (r.realization.functor.obj (ScalarLocalization.mk M)).obj
```

```lean
def IsBalancedPowerFamily
    (c : ∀ d : ℕ, integralPower X l d ⟶
      (Mod.comap (integralToQbar X l)).obj (tateTwistNat X l d)) : Prop :=
  (c 0).hom = integralToQbar X l ∧ ∀ d : ℕ,
    Mod.tensorObjπ (integralPower X l d) (tateModule X l) ≫ (c (d + 1)).hom =
      ((c d).hom ⊗ₘ
        ((Mod.extendRestrictAdjunction (integralToQbar X l)).unit.app
          (tateModule X l)).hom) ≫
        Mod.tensorObjπ (tateTwistNat X l d) (tateTwistOne X l)
```

```lean
abbrev ordinaryRestriction (r : At l (LiftedQ.{u} l) X) :=
  Mod.comap (rationalToQbar X l) ⋙
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor ⋙
      pbcRestrict (scalarMap X l r)
```

```lean
def restrictionComparison (r : At l (LiftedQ.{u} l) X) :
    (ordinaryRestriction X l r).mapDerivedCategory ≅ ambientRestriction X l r :=
  Functor.mapDerivedCategoryCompIso
      (Mod.comap (rationalToQbar X l) ⋙
        (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor)
      (pbcRestrict (scalarMap X l r)) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryCompIso (Mod.comap (rationalToQbar X l))
        (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor)
      (pbcDerivedRestrict (scalarMap X l r))
```

```lean
def reconstructedProjection (r : At l (LiftedQ.{u} l) X) (d n : ℕ) :
    reconstructed X l r d ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        ((encodedTower X l r d).obj (op n)) :=
  (completedRlimProjection X (CompletedRing X l) n).app
      ((DerivedCategory.singleFunctor _ 0).obj (encodedTower X l r d)) ≫
    ((reductionTowerEvaluation X
      (reductionModuleRing X (CompletedRing X l)) n).mapDerivedCategorySingleFunctor 0).hom.app _
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

There were no declarations named tateRlim, tateRlimProjection, singleDerivedProjection.

## New

```lean
def tateRlim (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    DerivedCategory (reductionTowerCategory X (reductionModuleRing X B)) ⥤
      reductionDerivedCategory X B :=
  completedRlim X B
```

```lean
def tateRlimProjection (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (n : ℕ) :
    tateRlim X B ⟶ reductionTowerDerivedEvaluation X (reductionModuleRing X B) n :=
  completedRlimProjection X B n
```

```lean
def singleDerivedProjection {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (L : DerivedCategory C ⥤ DerivedCategory D) (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (π : L ⟶ F.mapDerivedCategory) (N : C) :
    L.obj ((DerivedCategory.singleFunctor C 0).obj N) ⟶
      (DerivedCategory.singleFunctor D 0).obj (F.obj N) :=
  π.app ((DerivedCategory.singleFunctor C 0).obj N) ≫
    (F.mapDerivedCategorySingleFunctor 0).hom.app N
```

```lean
def integralEncoding (r : At l (LiftedQ.{u} l) X) :
    IntegralModules X l ≌ pbcModules X (CompletedRing X l) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) (R X l)).trans
    (ringModuleEquivalenceOfIso X
      ((adicLisseForget X).mapIso (integralComparison X l r)).symm)
```

```lean
def encodedTower (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    ℕᵒᵖ ⥤ pbcModules X (CompletedRing X l) :=
  finiteTower X l d ⋙ (integralEncoding X l r).functor
```

```lean
def reconstructed (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    reductionDerivedCategory X (CompletedRing X l) :=
  (tateRlim X (CompletedRing X l)).obj
    ((DerivedCategory.singleFunctor _ 0).obj (encodedTower X l r d))
```

```lean
def shiftedReconstructed (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    reductionDerivedCategory X (CompletedRing X l) :=
  (shiftFunctor _ (2 * d : ℤ)).obj (reconstructed X l r d)
```

```lean
def limitAdjunction :
    (Functor.const ℕᵒᵖ :
      pbcModules X (CompletedRing X l) ⥤ _).mapDerivedCategory ⊣
      tateRlim X (CompletedRing X l) :=
  (constLimAdj : (Functor.const ℕᵒᵖ :
    pbcModules X (CompletedRing X l) ⥤ _) ⊣
      completedTowerLimit X (CompletedRing X l)).mapDerivedCategoryRightDerivedAdjunction
```

```lean
def derivedAugmentation (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    (DerivedCategory.singleFunctor (pbcModules X (CompletedRing X l)) 0).obj
      ((integralEncoding X l r).functor.obj (integralPower X l d)) ⟶
        reconstructed X l r d :=
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
def scalarMap (r : At l (LiftedQ.{u} l) X) :
    CompletedRing X l ⟶ rationalCoefficientSheaf l X (LiftedQ.{u} l) :=
  r.integralIso.hom ≫ r.inclusion
```

```lean
def rationalDerivedExtension :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (Coefficient (LiftedQ.{u} l) X)) ⥤
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :=
  let left {A B : Type (u + 2)} [Category.{u + 1} A] [Category.{u + 1} B]
      {F : A ⥤ B} {G : B ⥤ A} (_ : F ⊣ G) : A ⥤ B := F
  left (Mod.derivedExtendMapDerivedCategoryAdjunction
    (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (rationalToQbar X l))
```

```lean
abbrev ambientRealization (r : At l (LiftedQ.{u} l) X) :
    reductionDerivedCategory X (CompletedRing X l) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :=
  pbcDerivedExtend (scalarMap X l r) ⋙
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.inverse ⋙
      (rationalDerivedExtension X l)
```

```lean
abbrev ambientRestriction (r : At l (LiftedQ.{u} l) X) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) ⥤
        reductionDerivedCategory X (CompletedRing X l) :=
  (Mod.comap (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (rationalToQbar X l)).mapDerivedCategory ⋙
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.functor ⋙
      pbcDerivedRestrict (scalarMap X l r)
```

```lean
def scalarAdjunction (r : At l (LiftedQ.{u} l) X) :
    ambientRealization X l r ⊣ ambientRestriction X l r :=
  ((pbcDerivedScalarAdjunction (scalarMap X l r)).comp
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.symm.toAdjunction).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (rationalToQbar X l))
```

```lean
def realized (r : At l (LiftedQ.{u} l) X) (M : Integral l (LiftedQ.{u} l) X) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :=
  (rationalDerivedExtension X l).obj
    (r.realization.functor.obj (ScalarLocalization.mk M)).obj
```

```lean
def IsBalancedPowerFamily
    (c : ∀ d : ℕ, integralPower X l d ⟶
      (Mod.comap (integralToQbar X l)).obj (tateTwistNat X l d)) : Prop :=
  (c 0).hom = integralToQbar X l ∧ ∀ d : ℕ,
    Mod.tensorObjπ (integralPower X l d) (tateModule X l) ≫ (c (d + 1)).hom =
      ((c d).hom ⊗ₘ
        ((Mod.extendRestrictAdjunction
          (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (integralToQbar X l)).unit.app
          (tateModule X l)).hom) ≫
        Mod.tensorObjπ (tateTwistNat X l d) (tateTwistOne X l)

section BalancedTensor

open CategoryTheory.MonObj

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorLeft M)]
  [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorRight M)]
  {A B : C} [MonObj A] [MonObj B] [commA : IsCommMonObj A] [commB : IsCommMonObj B]
  (φ : A ⟶ B) [IsMonHom φ]

omit [MonObj A] [IsCommMonObj A] [IsMonHom φ] in
open CategoryTheory.BraidedCategory in
```

```lean
abbrev ordinaryRestriction (r : At l (LiftedQ.{u} l) X) :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) ⥤
        pbcModules X (CompletedRing X l) :=
  Mod.comap (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (rationalToQbar X l) ⋙
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor ⋙
      pbcRestrict (scalarMap X l r)
```

```lean
def restrictionComparison (r : At l (LiftedQ.{u} l) X) :
    (ordinaryRestriction X l r).mapDerivedCategory ≅ ambientRestriction X l r :=
  Functor.mapDerivedCategoryCompIso
      (Mod.comap (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (rationalToQbar X l) ⋙
        (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor)
      (pbcRestrict (scalarMap X l r)) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryCompIso
        (Mod.comap (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (rationalToQbar X l))
        (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor)
      (pbcDerivedRestrict (scalarMap X l r))
```

```lean
def reconstructedProjection (r : At l (LiftedQ.{u} l) X) (d n : ℕ) :
    reconstructed X l r d ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        ((encodedTower X l r d).obj (op n)) :=
  singleDerivedProjection (tateRlim X (CompletedRing X l))
    (reductionTowerEvaluation X (reductionModuleRing X (CompletedRing X l)) n)
    (tateRlimProjection X (CompletedRing X l) n) (encodedTower X l r d)
```

```lean
noncomputable instance ambientRealizationCommShift (r : At l (LiftedQ.{u} l) X) :
    (ambientRealization X l r).CommShift ℤ := by
  let restrictShift {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
      (φ : A ⟶ B) : (pbcDerivedRestrict φ).CommShift ℤ := by
    unfold pbcDerivedRestrict
    infer_instance
  let extendShift {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
      (φ : A ⟶ B) : (pbcDerivedExtend φ).CommShift ℤ := by
    letI : (pbcDerivedRestrict φ).CommShift ℤ := restrictShift φ
    exact (pbcDerivedScalarAdjunction φ).leftAdjointCommShift ℤ
  letI : (pbcDerivedExtend (scalarMap X l r)).CommShift ℤ :=
    extendShift (scalarMap X l r)
  let G : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) ⥤
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (Coefficient (LiftedQ.{u} l) X) :=
    Mod.comap (C := Sheaf (ProEt.topology X) Ab.{u + 1}) (rationalToQbar X l)
  letI : G.mapDerivedCategory.CommShift ℤ := inferInstance
  letI : (rationalDerivedExtension X l).CommShift ℤ := by
    unfold rationalDerivedExtension
    exact (Mod.derivedExtendMapDerivedCategoryAdjunction (C := Sheaf (ProEt.topology X) Ab.{u + 1})
      (rationalToQbar X l)).leftAdjointCommShift ℤ
  unfold ambientRealization
  infer_instance
```

## Users

The read-only downstream scan lists the six importers below. Textual declaration
search finds no downstream use of the changed definition bodies. All retained
objects and morphisms are the original constructions, with explicit result types
and named interfaces for the same derived-limit and projection formulas.
Checks importing the new compiled module compare the shift structure, derived
scalar functor and scalar adjunction with their original formulas by rfl.
Generic checks compare tateRlim, tateRlimProjection and singleDerivedProjection
with their original formulas by rfl, and check the reconstructed object.
These defining equalities preserve the projection and augmentation constructions.
Every downstream statement retains its meaning. All six unchanged consumer sources
compiled against the newly built module.
No consumer adaptation is required. Holders are from the current shared snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedTateRealization | A2, this assignment | Elaborate the same canonical data with explicit types, named interfaces and generic functions. |
| Sheaf.Paper.CondensedOpenCoefficientModels | No claim in shared snapshot | Same public interface and canonical data; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | No claim in shared snapshot | Same public interface and canonical data; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealization | No claim in shared snapshot | Same public interface and canonical data; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | No claim in shared snapshot | Same public interface and canonical data; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | No claim in shared snapshot | Same public interface and canonical data; no adaptation. |
| Sheaf.Paper.CondensedOpenUnitComparison | No claim in shared snapshot | Same public interface and canonical data; no adaptation. |

## Status

landed 20261026T022715-L-394496 2026-10-26 (merge of deliver/A2/Sheaf.Paper.CondensedTateRealization)
