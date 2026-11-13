/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # Essential image of a restricted open direct image

Source: Stacks Project, Tags 08FE and 08DG.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleIsoEquivalence {T U : Scheme.{u}} (s : T ≅ U) :
    SheafOfModules.{u} (moduleRings T.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings U.toRingedSpace) :=
  CategoryTheory.Equivalence.mk (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
    (SheafOfModules.pushforward s.inv.toRingCatSheafHom)
    ((Scheme.Modules.pushforwardComp s.hom s.inv ≪≫
      Scheme.Modules.pushforwardCongr s.hom_inv_id ≪≫ Scheme.Modules.pushforwardId T).symm)
    (Scheme.Modules.pushforwardComp s.inv s.hom ≪≫
      Scheme.Modules.pushforwardCongr s.inv_hom_id ≪≫ Scheme.Modules.pushforwardId U)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in
-- Transport through the open and isomorphism adjunctions needs more instance search.
-- The nested derived-functor comparisons require a larger elaboration budget.

/-- The restriction to O of an open direct image from P is in the essential image
of the right adjoint to restriction from O to W = O ∩ P (Stacks, Tags 08FE and 08DG). -/
theorem derived_open_intersection_mem_essImage
    (X : Scheme.{u}) (O P W : X.Opens) (hW : W = O ⊓ P) (iO : W ⟶ O)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings O.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings P.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (S : schemeDerivedCategory W.toScheme ⥤ schemeDerivedCategory O.toScheme)
    (adj : (schemeOpenOverlapRestriction X iO).mapDerivedCategory ⊣ S)
    (B : schemeDerivedCategory P.toScheme) :
    S.essImage ((schemeOpenRestriction X O).mapDerivedCategory.obj
      ((schemeDerivedDirectImage P.ι).obj B)) := by
  classical
  let V := P.ι ⁻¹ᵁ O
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  let g := P.ι ∣_ O
  let k := X.homOfLE (leOfHom iO)
  have himage : P.ι ''ᵁ V = W := by
    dsimp [V]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_comm, ← hW]
  let q : V.toScheme ≅ W.toScheme :=
    P.ι.isoImage V ≪≫ X.isoOfEq himage
  have hq : q.hom ≫ W.ι = V.ι ≫ P.ι := by
    dsimp [q]
    simp only [Category.assoc, Scheme.isoOfEq_hom_ι,
      Scheme.Hom.isoImage_hom_ι]
  have hfac : q.inv ≫ g = k := by
    apply (cancel_mono O.ι).mp
    rw [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
    rw [← hq]
    simp
  let e := moduleIsoEquivalence q
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let c : e.functor ≅ Scheme.Modules.restrictFunctor q.inv :=
    e.toAdjunction.leftAdjointUniq (Scheme.Modules.restrictAdjunction q.inv)
  let t : schemeOpenOverlapRestriction X iO ≅ Scheme.Modules.restrictFunctor k :=
    Functor.isoWhiskerLeft (Scheme.Modules.overEquiv O).inverse
        (Scheme.Modules.overMapCompOverEquiv iO) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.overEquiv O).counitIso _ ≪≫
      Functor.leftUnitor _
  let z : Scheme.Modules.restrictFunctor g ⋙ e.functor ≅
      schemeOpenOverlapRestriction X iO :=
    Functor.isoWhiskerLeft _ c ≪≫
      (Scheme.Modules.restrictFunctorComp q.inv g).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hfac ≪≫ t.symm
  let rg : SheafOfModules.{u} (moduleRings O.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
    Scheme.Modules.restrictFunctor g
  let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
  let a0 : rg ⊣ G := Scheme.Modules.restrictAdjunction g
  have : PreservesFiniteLimits (rg ⋙ e.functor) :=
    preservesFiniteLimits_of_natIso z.symm
  have : PreservesFiniteColimits (rg ⋙ e.functor) :=
    preservesFiniteColimits_of_natIso z.symm
  have : PreservesFiniteLimits rg :=
    preservesFiniteLimits_of_reflects_of_preserves rg e.functor
  have : PreservesFiniteColimits rg :=
    preservesFiniteColimits_of_reflects_of_preserves rg e.functor
  have : rg.Additive := Functor.additive_of_preserves_binary_products _
  let E := e.mapDerivedCategory
  let a := a0.mapDerivedCategoryRightDerivedAdjunction
  let zD : rg.mapDerivedCategory ⋙ E.functor ≅
      (schemeOpenOverlapRestriction X iO).mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso rg e.functor) ≪≫
      Functor.mapDerivedCategoryNatIso z
  let b := (a.comp E.toAdjunction).ofNatIsoLeft zD
  let j := b.rightAdjointUniq adj
  obtain ⟨bc⟩ := schemeDerivedDirectImage_openRestriction P.ι O
  let M := (schemeOpenRestriction P.toScheme V).mapDerivedCategory.obj B
  refine ⟨E.functor.obj M, ⟨?_⟩⟩
  exact (j.app (E.functor.obj M)).symm ≪≫
    (schemeDerivedDirectImage g).mapIso (E.unitIso.symm.app M) ≪≫ (bc.app B).symm

end AlgebraicGeometry
