/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Homology of products in the derived category

Let `C` be an abelian category with K-injective resolutions in which products of shape `J`
exist and are exact (AB4* for products of shape `J`), for instance sheaves of modules on the
pro-étale site and countable products. Then the homology functors `D(C) ⥤ C` preserve products
of shape `J` (`DerivedCategory.preservesLimitsOfShape_homologyFunctor_discrete`): a product of
objects of `D(C)` is computed by the degreewise product of K-injective representatives, and
homology commutes with degreewise products because products are exact.

## Main results

- `HomologicalComplex.isLimitHomologyFunctorMapCone`: homology of complexes commutes with exact
  limits.
- `DerivedCategory.isLimitFanQhOfIsKInjective`: the degreewise product of K-injective complexes
  is a product in `D(C)`.
- `DerivedCategory.preservesLimitsOfShape_homologyFunctor_discrete`: the homology functors of
  `D(C)` preserve products of shape `J`.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Limits

/-- A fan which is isomorphic, termwise and on its point, to a limit fan is a limit fan. -/
def Fan.isLimitOfIsoOfIsLimit {C : Type*} [Category C] {β : Type*} {X Y : β → C}
    (e : ∀ j, X j ≅ Y j) {P : Fan X} (hP : IsLimit P) (Q : Fan Y) (eπ : P.pt ≅ Q.pt)
    (w : ∀ j, eπ.hom ≫ Q.proj j = P.proj j ≫ (e j).hom) : IsLimit Q :=
  Fan.IsLimit.mk _ (fun s ↦ Fan.IsLimit.lift hP (fun j ↦ s.proj j ≫ (e j).inv) ≫ eπ.hom)
    (fun s j ↦ by rw [assoc, w, Fan.IsLimit.fac_assoc, assoc, Iso.inv_hom_id, comp_id])
    (fun s m hm ↦ by
      rw [← cancel_mono eπ.inv, assoc, Iso.hom_inv_id, comp_id]
      refine Fan.IsLimit.hom_ext hP _ _ fun j ↦ ?_
      rw [Fan.IsLimit.fac, assoc, ← cancel_mono (e j).hom, assoc, assoc, ← w,
        Iso.inv_hom_id_assoc, hm, assoc, Iso.inv_hom_id, comp_id])

end CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type*} [Category C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {J : Type*} [Category J] [HasLimitsOfShape J C] [HasExactLimitsOfShape J C]

/-- If limits of shape `J` are exact in `C`, the homology of a limit of complexes is the limit
of their homologies. -/
noncomputable def isLimitHomologyFunctorMapCone {F : J ⥤ HomologicalComplex C c} {s : Cone F}
    (hs : IsLimit s) (i : ι) : IsLimit ((homologyFunctor C c i).mapCone s) :=
  ShortComplex.isLimitHomologyFunctorMapCone (F := F ⋙ shortComplexFunctor C c i)
    (c := (shortComplexFunctor C c i).mapCone s)
    (ShortComplex.isLimitOfIsLimitπ _ (isLimitOfPreserves (eval C c (c.prev i)) hs)
      (isLimitOfPreserves (eval C c i) hs) (isLimitOfPreserves (eval C c (c.next i)) hs))

instance preservesLimitsOfShape_homologyFunctor (i : ι) :
    PreservesLimitsOfShape J (homologyFunctor C c i) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limit.isLimit F)
    (isLimitHomologyFunctorMapCone (limit.isLimit F) i)

end HomologicalComplex

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  {J : Type*} [HasLimitsOfShape (Discrete J) C]

/-- A degreewise product of complexes which are K-injective (right orthogonal to the acyclic
complexes in the homotopy category) is a product in the derived category. -/
noncomputable def isLimitFanQhOfIsKInjective {I : J → CochainComplex C ℤ}
    (hI : ∀ j, (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
      ((HomotopyCategory.quotient C (.up ℤ)).obj (I j)))
    {P : Fan I} (hP : IsLimit P) :
    IsLimit (Fan.mk (Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj P.pt))
      fun j ↦ Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map (P.proj j))) := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  have hq := HomotopyCategory.isLimitFanQuotient C (.up ℤ) hP
  have hPI : (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal (q.obj P.pt) :=
    fun X f hX ↦ Fan.IsLimit.hom_ext hq _ _ fun j ↦ by
      rw [zero_comp]
      exact hI j _ hX
  have hbij (Y : HomotopyCategory C (.up ℤ)) (T : HomotopyCategory C (.up ℤ))
      (hT : (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal T) :
      Function.Bijective (Qh.map : (Y ⟶ T) → _) :=
    hT.map_bijective_of_isTriangulated _ _
  refine Fan.IsLimit.mk _ (fun s ↦ ?_) (fun s j ↦ ?_) (fun s m hm ↦ ?_)
  all_goals
    let Y := Qh.objPreimage s.pt
    let e : Qh.obj Y ≅ s.pt := Qh.objObjPreimageIso s.pt
    have g (j : J) : ∃ g : Y ⟶ q.obj (I j), Qh.map g = e.hom ≫ s.proj j :=
      (hbij Y _ (hI j)).2 _
  · exact e.inv ≫ Qh.map (Fan.IsLimit.lift hq fun j ↦ (g j).choose)
  · change (e.inv ≫ Qh.map (Fan.IsLimit.lift hq fun j ↦ (g j).choose)) ≫
      Qh.map (q.map (P.proj j)) = s.proj j
    rw [assoc, ← Functor.map_comp]
    erw [Fan.IsLimit.fac hq (fun j ↦ (g j).choose) j]
    rw [(g j).choose_spec, Iso.inv_hom_id_assoc]
  · obtain ⟨m', hm'⟩ := (hbij Y _ hPI).2 (e.hom ≫ m)
    have : m' = Fan.IsLimit.lift hq fun j ↦ (g j).choose :=
      Fan.IsLimit.hom_ext hq _ _ fun j ↦ by
        erw [Fan.IsLimit.fac hq (fun j ↦ (g j).choose) j]
        refine (hbij Y _ (hI j)).1 ?_
        change Qh.map (m' ≫ q.map (P.proj j)) = _
        rw [(g j).choose_spec, Functor.map_comp, hm', assoc]
        exact congrArg (e.hom ≫ ·) (hm j)
    dsimp only
    rw [← this, hm', Iso.inv_hom_id_assoc]

variable [Abelian.HasKInjectiveResolutions C] [HasExactLimitsOfShape (Discrete J) C]

/-- The homology functors of the derived category preserve products of shape `J` when these
products are exact in `C`. -/
instance preservesLimitsOfShape_homologyFunctor_discrete (n : ℤ) :
    PreservesLimitsOfShape (Discrete J) (homologyFunctor C n) where
  preservesLimit {F} := by
    let q := HomotopyCategory.quotient C (.up ℤ)
    let E := HomotopyCategory.KInjectives.equivalence C
    let T (j : J) := E.inverse.obj (F.obj ⟨j⟩)
    let I (j : J) : CochainComplex C ℤ := (T j).obj.as
    let ε : q ⋙ Qh ⋙ homologyFunctor C n ≅ HomologicalComplex.homologyFunctor C _ n :=
      Functor.isoWhiskerLeft q (homologyFunctorFactorsh C n) ≪≫
        HomotopyCategory.homologyFunctorFactors C _ n
    let c (j : J) : Qh.obj (q.obj (I j)) ≅ F.obj ⟨j⟩ := E.counitIso.app (F.obj ⟨j⟩)
    have hP := productIsProduct I
    have hD := isLimitFanQhOfIsKInjective (fun j ↦ (T j).property) hP
    -- A limit fan over the family `j ↦ F.obj ⟨j⟩`, and its image under homology.
    let P' : Fan fun j ↦ F.obj ⟨j⟩ :=
      Fan.mk (Qh.obj (q.obj (∏ᶜ I))) fun j ↦ Qh.map (q.map (Pi.π I j)) ≫ (c j).hom
    have hP' : IsLimit P' :=
      Fan.isLimitOfIsoOfIsLimit (fun j ↦ c j) hD P' (Iso.refl _) fun j ↦ by
        rw [Iso.refl_hom, id_comp]; rfl
    have hH : IsLimit (Fan.mk ((homologyFunctor C n).obj P'.pt)
        fun j ↦ (homologyFunctor C n).map (P'.proj j)) :=
      Fan.isLimitOfIsoOfIsLimit
        (fun j ↦ (ε.app (I j)).symm ≪≫ (homologyFunctor C n).mapIso (c j))
        (isLimitFanMkObjOfIsLimit (HomologicalComplex.homologyFunctor C _ n) _ _ hP)
        _ (ε.app (∏ᶜ I)).symm fun j ↦ by
          have := ε.inv.naturality (Pi.π I j)
          change ε.inv.app _ ≫ (homologyFunctor C n).map (Qh.map (q.map (Pi.π I j)) ≫ (c j).hom) =
            (HomologicalComplex.homologyFunctor C _ n).map (Pi.π I j) ≫ ε.inv.app (I j) ≫
              (homologyFunctor C n).map (c j).hom
          rw [Functor.map_comp, reassoc_of% this]
    have : PreservesLimit (Discrete.functor fun j ↦ F.obj ⟨j⟩) (homologyFunctor C n) :=
      preservesLimit_of_preserves_limit_cone hP'
        ((isLimitMapConeFanMkEquiv _ _ _).symm hH)
    exact preservesLimit_of_iso_diagram (K₁ := Discrete.functor fun j ↦ F.obj ⟨j⟩) _
      Discrete.natIsoFunctor.symm

end DerivedCategory
