/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
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
  `H^n(R⁺F(X[0])) ≅ R^n F X`; it is natural in `X`
  (`CategoryTheory.Functor.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso`).
- `CategoryTheory.Functor.nonempty_homology_rightDerivedFunctorPlus_obj_Q_iso`: if `L` is a
  bounded below complex of `F`-acyclic objects and `F` is left exact, then
  `H^n(R⁺F(L)) ≅ H^n(F(L))`.
- `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic`: if `G` is left exact
  and `F` sends injective objects to `G`-acyclic objects, then `R⁺(F ⋙ G) ≅ R⁺F ⋙ R⁺G`.
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

/-- The isomorphism `DerivedCategory.Plus.homologyFunctorObjQIso` is natural. -/
@[reassoc]
lemma homologyFunctorObjQIso_hom_naturality {K L : CochainComplex.Plus C} (g : K ⟶ L) (n : ℤ) :
    (homologyFunctor C n).map (Q.map g) ≫ (homologyFunctorObjQIso L n).hom =
      (homologyFunctorObjQIso K n).hom ≫ HomologicalComplex.homologyMap g.hom n := by
  have h₁ := (DerivedCategory.homologyFunctorFactorsh C n).hom.naturality
    ((HomotopyCategory.quotient C _).map g.hom)
  have h₂ := (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.naturality g.hom
  dsimp at h₁ h₂
  simp only [homologyFunctorObjQIso]
  change (DerivedCategory.homologyFunctor C n).map
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map g.hom)) ≫ _ = _
  erw [Iso.trans_hom, Iso.trans_hom, reassoc_of% h₁, h₂]
  simp only [Category.assoc]
  rfl

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

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `R^n F X ≅ H^n(F(I))` is natural with respect to morphisms of injective
resolutions. -/
lemma isoRightDerivedObjCochainComplex_inv_naturality {X Y : C} {f : X ⟶ Y}
    (R : InjectiveResolution X) {R' : InjectiveResolution Y} (φ : R.Hom R' f) (F : C ⥤ D)
    [F.Additive] (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ.hom') n ≫
        (R'.isoRightDerivedObjCochainComplex F n).inv =
      (R.isoRightDerivedObjCochainComplex F n).inv ≫ (F.rightDerived n).map f := by
  rw [F.rightDerived_map_eq n f φ.hom φ.ι_comp_hom]
  have h : (F.mapHomologicalComplex _).map φ.hom' ≫
      (R'.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom =
      (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex _).map φ.hom)
          ComplexShape.embeddingUpNat := by
    ext i
    exact HomologicalComplex.mapExtensIso_hom_f_naturality _ _ _ _
  simp only [InjectiveResolution.isoRightDerivedObjCochainComplex, Iso.trans_inv, Iso.symm_inv,
    Category.assoc]
  simp only [Functor.mapIso_inv, Iso.symm_inv, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map, Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp_assoc, h, HomologicalComplex.homologyMap_comp_assoc,
    HomologicalComplex.extendHomologyIso_hom_naturality_assoc]

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

/-- The morphism `F(I) ⟶ F(J)` of complexes induced by a morphism of the chosen injective
resolutions `I` of `X` and `J` of `Y`. -/
noncomputable def rightDerivedPlusComplexMap {X Y : C} {f : X ⟶ Y}
    (φ : (injectiveResolution X).Hom (injectiveResolution Y) f) :
    F.rightDerivedPlusComplex X ⟶ F.rightDerivedPlusComplex Y :=
  ObjectProperty.homMk ((F.mapHomologicalComplex _).map φ.hom')

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `R⁺F(X[0]) ≅ F(I)` is compatible with morphisms of injective
resolutions. -/
lemma rightDerivedFunctorPlusObjSingleFunctorIsoQ_hom_naturality {X Y : C} {f : X ⟶ Y}
    (φ : (injectiveResolution X).Hom (injectiveResolution Y) f) :
    F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f) ≫
        (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ Y).hom =
      (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ X).hom ≫
        DerivedCategory.Plus.Q.map (F.rightDerivedPlusComplexMap φ) := by
  let LX : CochainComplex.Plus C := ⟨(injectiveResolution X).cochainComplex, 0, inferInstance⟩
  let LY : CochainComplex.Plus C := ⟨(injectiveResolution Y).cochainComplex, 0, inferInstance⟩
  let g : LX ⟶ LY := ObjectProperty.homMk φ.hom'
  have h₁ := F.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient C).map g)
  have h₂ : (DerivedCategory.Plus.singleFunctor C 0).map f ≫
      (DerivedCategory.Plus.ι.preimageIso (X := (DerivedCategory.Plus.singleFunctor C 0).obj Y)
        (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj LY))
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app Y ≪≫
          asIso (DerivedCategory.Q.map (injectiveResolution Y).ι') ≪≫
          (DerivedCategory.quotientCompQhIso C).symm.app _)).hom =
      (DerivedCategory.Plus.ι.preimageIso (X := (DerivedCategory.Plus.singleFunctor C 0).obj X)
        (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj LX))
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app X ≪≫
          asIso (DerivedCategory.Q.map (injectiveResolution X).ι') ≪≫
          (DerivedCategory.quotientCompQhIso C).symm.app _)).hom ≫
        DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map g) := by
    apply DerivedCategory.Plus.ι.map_injective
    have := (DerivedCategory.quotientCompQhIso C).inv.naturality φ.hom'
    simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
    dsimp at this ⊢
    change (DerivedCategory.singleFunctor C 0).map f ≫ _ =
      _ ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map φ.hom')
    rw [Category.assoc, Category.assoc, ← this,
      (DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality_assoc]
    simp only [Functor.comp_map, ← Functor.map_comp_assoc,
      InjectiveResolution.Hom.ι'_comp_hom']
  dsimp [rightDerivedFunctorPlusObjSingleFunctorIsoQ]
  rw [← F.rightDerivedFunctorPlus.map_comp_assoc, h₂, Functor.map_comp, Category.assoc,
    Category.assoc]
  congr 1
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  exact h₁.symm

/-- The isomorphism `H^n(R⁺F(X[0])) ≅ R^n F X` is natural in `X`. -/
@[reassoc]
lemma homologyRightDerivedFunctorPlusObjSingleFunctorIso_hom_naturality {X Y : C} (f : X ⟶ Y)
    (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor D n).map
        (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f)) ≫
      (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso Y n).hom =
    (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso X n).hom ≫ (F.rightDerived n).map f := by
  let φ : (injectiveResolution X).Hom (injectiveResolution Y) f :=
    ⟨InjectiveResolution.desc f _ _, by simp [InjectiveResolution.desc_commutes_zero]⟩
  simp only [homologyRightDerivedFunctorPlusObjSingleFunctorIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, rightDerivedFunctorPlusObjSingleFunctorIsoQ_hom_naturality F φ,
    Functor.map_comp, Category.assoc]
  congr 1
  have key := (injectiveResolution X).isoRightDerivedObjCochainComplex_inv_naturality φ F n
  have key₂ := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality
    (F.rightDerivedPlusComplexMap φ) n
  change _ ≫ (DerivedCategory.Plus.homologyFunctorObjQIso (F.rightDerivedPlusComplex Y) n).hom ≫
      ((injectiveResolution Y).isoRightDerivedObjCochainComplex F n).inv =
    (DerivedCategory.Plus.homologyFunctorObjQIso (F.rightDerivedPlusComplex X) n).hom ≫
      ((injectiveResolution X).isoRightDerivedObjCochainComplex F n).inv ≫ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key₂).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) key)))

/-- The isomorphism `H^n(R⁺F(X[0])) ≅ R^n F X` of
`Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso`, as a natural isomorphism of
functors `C ⥤ D`. -/
noncomputable def singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso (n : ℕ) :
    DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor D n ≅ F.rightDerived n :=
  NatIso.ofComponents (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso · n)
    (fun f ↦ F.homologyRightDerivedFunctorPlusObjSingleFunctorIso_hom_naturality f n)

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

/-- **Acyclic complexes compute `R⁺F`, at the level of the unit.** If `F` is left exact and `L`
is a bounded below complex of `F`-acyclic objects, then the unit `F(L) ⟶ R⁺F(L)` is an
isomorphism in `DerivedCategory.Plus D`. Choose a quasi-isomorphism `i : L ⟶ T` to a bounded
below complex of injectives. In the naturality square of the unit
```
F(L) ----unit----> R⁺F(L)
 |                   |
F(i)              R⁺F(i)
 v                   v
F(T) ----unit----> R⁺F(T)
```
the bottom map is an isomorphism as `T` is injective, `R⁺F(i)` is an isomorphism as `i` is a
quasi-isomorphism, and `F(i)` is an isomorphism by `Functor.quasiIso_map_of_rightAcyclic`. -/
theorem isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic [PreservesFiniteLimits F]
    (L : CochainComplex.Plus C) (hL : ∀ n, F.rightAcyclic (L.obj.X n)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj L)) := by
  obtain ⟨a, ha⟩ := L.2
  obtain ⟨T, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective L a
  let T' := (InjectiveObject.ι C).mapCochainComplexPlus.obj T
  have : QuasiIso i.hom := hi
  have : ∀ n, Injective (T'.obj.X n) := fun n ↦ (T.obj.X n).2
  have : T'.obj.IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ _ _).2 ‹_›
  have hFi := F.quasiIso_map_of_rightAcyclic i.hom a hL
    (fun n ↦ F.rightAcyclic_of_injective _)
  have h₁ : IsIso (DerivedCategory.Plus.Qh.map
      (F.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient C).map i))) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hFi)
  have h₂ : IsIso (F.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i))) := by
    have : IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i)) :=
      Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C) _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hi)
    infer_instance
  have h₃ : IsIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient C).obj T')) := inferInstance
  have hnat := F.rightDerivedFunctorPlusUnit.naturality ((HomotopyCategory.Plus.quotient C).map i)
  dsimp only [Functor.comp_map] at hnat
  have : IsIso (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj L) ≫
      F.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i))) := by
    rw [← hnat]; infer_instance
  exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorPlus.map
    (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i)))

end

section Composition

variable {E : Type*} [Category* E] [Abelian E] [EnoughInjectives D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G]

/-- If `G` is left exact and `F` sends injective objects to `G`-acyclic objects, then
`R⁺F ⋙ R⁺G`, with the composite unit, is a right derived functor of `F ⋙ G`: on a bounded below
complex `K` of injectives the unit of `R⁺F` is an isomorphism, and so is the unit of `R⁺G` at
the complex `F(K)` of `G`-acyclic objects
(`Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`). -/
lemma isRightDerivedFunctor_rightDerivedFunctorPlus_comp_of_rightAcyclic
    (hFG : ∀ (I : C) [Injective I], G.rightAcyclic (F.obj I)) :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (rightDerivedFunctorPlusCompUnit F G) (HomotopyCategory.Plus.quasiIso C) := by
  refine (HomotopyCategory.Plus.localizerMorphism_derives
    ((F ⋙ G).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  set K : HomotopyCategory.Plus C := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X₁
  have h₁ : IsIso (F.rightDerivedFunctorPlusUnit.app K) := inferInstance
  let L : CochainComplex.Plus D := ⟨(F.mapHomotopyCategoryPlus.obj K).obj.as,
    (HomotopyCategory.plus_quotient_obj_iff _).1 (F.mapHomotopyCategoryPlus.obj K).property⟩
  have h₂ : IsIso (G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj K)) :=
    G.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic L (fun n ↦
      have : Injective (K.obj.as.X n) := inferInstanceAs (Injective ((X₁.obj.as.X n).obj))
      hFG (K.obj.as.X n))
  rw [rightDerivedFunctorPlusCompUnit_app]
  infer_instance

/-- **Composition of bounded below right derived functors with acyclicity.** If `G` is left
exact and `F` sends injective objects to `G`-acyclic objects, then the canonical comparison
`R⁺(F ⋙ G) ≅ R⁺F ⋙ R⁺G` is an isomorphism. -/
noncomputable def rightDerivedFunctorPlusCompIsoOfRightAcyclic
    (hFG : ∀ (I : C) [Injective I], G.rightAcyclic (F.obj I)) :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  have := F.isRightDerivedFunctor_rightDerivedFunctorPlus_comp_of_rightAcyclic G hFG
  rightDerivedUnique (F ⋙ G).rightDerivedFunctorPlus
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
    (F ⋙ G).rightDerivedFunctorPlusUnit (rightDerivedFunctorPlusCompUnit F G)
    (HomotopyCategory.Plus.quasiIso C)

end Composition

end Functor

end CategoryTheory
