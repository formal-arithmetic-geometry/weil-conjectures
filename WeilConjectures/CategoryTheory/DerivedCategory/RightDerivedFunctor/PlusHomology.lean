/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Homology of the bounded below right derived functor

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough
injectives. We compare the homology of `F.rightDerivedFunctorPlus` with the classical right
derived functors `F.rightDerived`, and we compute it on bounded below complexes of `F`-acyclic
objects.

## Main results

- `CategoryTheory.InjectiveResolution.isoRightDerivedObjCochainComplex`: `R^n F X` is the
  homology of `F` applied to the `ℤ`-indexed cochain complex of an injective resolution of `X`.
- `CategoryTheory.Functor.rightDerivedFunctorPlusObjSingleFunctorIsoQ`: `R⁺F(X[0])` is the image
  of the complex `F(I)` for an injective resolution `I` of `X`.
- `CategoryTheory.Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso`:
  `H^n(R⁺F(X[0])) ≅ R^n F X`.
- `CategoryTheory.Functor.nonempty_homology_rightDerivedFunctorPlus_obj_Q_iso`: if `L` is a
  bounded below complex of `F`-acyclic objects and `F` is left exact, then
  `H^n(R⁺F(L)) ≅ H^n(F(L))`.
-/

@[expose] public section

namespace DerivedCategory.Plus

open CategoryTheory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The homology of the image in `DerivedCategory.Plus C` of a bounded below cochain complex
is the homology of the complex. -/
noncomputable def homologyFunctorObjQIso (K : CochainComplex.Plus C) (n : ℤ) :
    (homologyFunctor C n).obj (Q.obj K) ≅ K.obj.homology n :=
  (DerivedCategory.homologyFunctorFactorsh C n).app _ ≪≫
    (HomotopyCategory.homologyFunctorFactors C _ n).app K.obj

end DerivedCategory.Plus

namespace CategoryTheory

open Limits ZeroObject

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

namespace InjectiveResolution

variable [HasInjectiveResolutions C]

/-- If `R` is an injective resolution of `X`, then `R^n F X` is the `n`-th homology of `F`
applied to the `ℤ`-indexed cochain complex `R.cochainComplex`. -/
noncomputable def isoRightDerivedObjCochainComplex {X : C} (R : InjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).obj X ≅
      ((F.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).homology n :=
  R.isoRightDerivedObj F n ≪≫
    (((F.mapHomologicalComplex _).obj R.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat rfl).symm ≪≫
    (HomologicalComplex.homologyFunctor D _ (n : ℤ)).mapIso
      (HomologicalComplex.mapExtendIso R.cocomplex ComplexShape.embeddingUpNat F).symm

end InjectiveResolution

namespace Functor

variable (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

section

variable [HasDerivedCategory C] [HasDerivedCategory D]

/-- If `L` is a bounded below complex of injective objects, the homology of `R⁺F(L)` is the
homology of `F(L)`. -/
noncomputable def homologyRightDerivedFunctorPlusObjQIsoOfInjective (L : CochainComplex.Plus C)
    [∀ n, Injective (L.obj.X n)] (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L)) ≅
      ((F.mapHomologicalComplex _).obj L.obj).homology n :=
  (DerivedCategory.Plus.homologyFunctor D n).mapIso
      (asIso (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj L))).symm ≪≫
    (DerivedCategory.homologyFunctorFactorsh D n).app _ ≪≫
    (HomotopyCategory.homologyFunctorFactors D _ n).app _

/-- The bounded below cochain complex `F(I)`, where `I` is the chosen injective resolution of
`X : C` (as a `ℤ`-indexed complex). Its image in `DerivedCategory.Plus D` is `R⁺F(X[0])`, see
`Functor.rightDerivedFunctorPlusObjSingleFunctorIsoQ`. -/
noncomputable def rightDerivedPlusComplex (X : C) : CochainComplex.Plus D :=
  ⟨(F.mapHomologicalComplex _).obj (injectiveResolution X).cochainComplex, 0, inferInstance⟩

/-- `R⁺F(X[0])` is the image in the derived category of the complex `F(I)`, where `I` is the
chosen injective resolution of `X`. -/
noncomputable def rightDerivedFunctorPlusObjSingleFunctorIsoQ (X : C) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≅
      DerivedCategory.Plus.Q.obj (F.rightDerivedPlusComplex X) :=
  let R := injectiveResolution X
  let L : CochainComplex.Plus C := ⟨R.cochainComplex, 0, inferInstance⟩
  have : ∀ n, Injective (L.obj.X n) := fun n ↦ inferInstanceAs (Injective (R.cochainComplex.X n))
  F.rightDerivedFunctorPlus.mapIso (DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app X ≪≫
      asIso (DerivedCategory.Q.map R.ι') ≪≫ (DerivedCategory.quotientCompQhIso C).symm.app _)) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj L))).symm

/-- The `n`-th homology of `R⁺F` applied to `X` placed in degree `0` is `R^n F X`. -/
noncomputable def homologyRightDerivedFunctorPlusObjSingleFunctorIso (X : C) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor D n).obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X)) ≅
      (F.rightDerived n).obj X :=
  (DerivedCategory.Plus.homologyFunctor D n).mapIso
      (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ X) ≪≫
    DerivedCategory.Plus.homologyFunctorObjQIso _ n ≪≫
    ((injectiveResolution X).isoRightDerivedObjCochainComplex F n).symm

/-- **Acyclic complexes compute `R⁺F`.** If `F` is left exact and `L` is a bounded below
complex of `F`-acyclic objects, then the homology of `R⁺F(L)` is the homology of `F(L)`. -/
theorem nonempty_homology_rightDerivedFunctorPlus_obj_Q_iso [PreservesFiniteLimits F]
    (L : CochainComplex.Plus C) (hL : ∀ n, F.rightAcyclic (L.obj.X n)) (n : ℤ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor D n).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L)) ≅
      ((F.mapHomologicalComplex _).obj L.obj).homology n) := by
  obtain ⟨a, ha⟩ := L.2
  obtain ⟨T, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective L a
  let T' := (InjectiveObject.ι C).mapCochainComplexPlus.obj T
  have : QuasiIso i.hom := hi
  have : ∀ n, Injective (T'.obj.X n) := fun n ↦ (T.obj.X n).2
  have : T'.obj.IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ _ _).2 ‹_›
  have := F.quasiIso_map_of_rightAcyclic i.hom a hL
    (fun n ↦ F.rightAcyclic_of_injective _)
  have : IsIso (DerivedCategory.Plus.Q.map i) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hi)
  exact ⟨(DerivedCategory.Plus.homologyFunctor D n).mapIso
      (F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map i))) ≪≫
    F.homologyRightDerivedFunctorPlusObjQIsoOfInjective T' n ≪≫
    (asIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map i.hom) n)).symm⟩

end

end Functor

end CategoryTheory
