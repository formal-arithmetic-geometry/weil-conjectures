/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkOutside
import WeilConjectures.AlgebraicGeometry.SupportedDerivedRestrictionZero
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact derived restriction has the original homology stalk at each point of the open.
Combine exact restriction/homology comparison with the over-site equivalence and
`Scheme.Modules.restrictStalkNatIso`. -/
private noncomputable def restrictionHomologyStalkIso.{z}
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{z}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (K : schemeDerivedCategory X) (n : ℤ) (x : U.toScheme) :
    TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj
        ((schemeOpenRestriction X U).mapDerivedCategory.obj K)).val.presheaf x ≅
    TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj K).val.presheaf x.val := by
  let H := Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor _ x
  let M := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K
  exact H.mapIso (((schemeOpenRestriction X U).mapDerivedCategoryHomologyFunctorIso n).symm.app K)
    ≪≫ H.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)
    ≪≫ (Scheme.Modules.restrictStalkNatIso U.ι x).app M

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Vanishing after open restriction implies vanishing of homology stalks on that open.
Apply homology and the additive stalk functor to the zero object, then use the stalk
comparison. -/
private theorem stalk_zero_of_restriction_zero.{z}
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{z}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (K : schemeDerivedCategory X)
    (hK : IsZero ((schemeOpenRestriction X U).mapDerivedCategory.obj K))
    (n : ℤ) (x : U.toScheme) :
    Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj K).val.presheaf x.val)) := by
  let H := Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor _ x
  have : (Scheme.Modules.toPresheaf U.toScheme).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hz := H.map_isZero ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).map_isZero hK)
  have hs := AddCommGrpCat.isZero_iff_subsingleton.mp hz
  let i := restrictionHomologyStalkIso X U K n x
  exact i.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp hs

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Open base change propagates cohomological support through derived direct image.
Restriction to the inverse image of the open complement of T is zero by supported
restriction. Open base change identifies restriction of the direct image with the
direct image of that zero object. Its homology stalks on the complement vanish. -/
private theorem direct_image_support
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) (hT : IsClosed T) (K : schemeDerivedCategory Y)
    (hK : ∀ (n : ℤ) (y : Y), f y ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj K).val.presheaf y))) :
    ∀ (n : ℤ) (x : X), x ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj
        ((schemeDerivedDirectImage f).obj K)).val.presheaf x)) := by
  let O : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  let V := f ⁻¹ᵁ O
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings O.toScheme.toRingedSpace))
  have hz := supported_derived_restriction_zero Y (f ⁻¹' T) V
    (by intro y hy; exact hy) K hK
  let e := Scheme.Modules.overEquiv V
  have hres : IsZero ((schemeOpenRestriction Y V).mapDerivedCategory.obj K) := by
    let D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)
    let F : SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V) ⥤ D := e.functor
    have : F.Additive := Functor.additive_of_preserves_binary_products _
    have : PreservesFiniteLimits
        (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V ⋙ F) :=
      comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits
        (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V ⋙ F) :=
      comp_preservesFiniteColimits _ _
    exact (F.mapDerivedCategory.map_isZero hz).of_iso
      ((Functor.mapDerivedCategoryCompIso
        (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V)
        (Equivalence.functor (C := SheafOfModules.{u}
          ((moduleRings Y.toRingedSpace).over V)) (D := D) e)).symm.app K)
  obtain ⟨bc⟩ := schemeDerivedDirectImage_openRestriction f O
  have hout : IsZero ((schemeOpenRestriction X O).mapDerivedCategory.obj
      ((schemeDerivedDirectImage f).obj K)) := by
    exact ((schemeDerivedDirectImage (f ∣_ O)).map_isZero hres).of_iso (bc.app K)
  intro n x hx
  exact stalk_zero_of_restriction_zero X O _ hout n ⟨x, hx⟩

/-- Derived direct image for an open immersion is fully faithful (Tag 08FE). -/
private noncomputable def open_direct_image_fullyFaithful
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    (schemeDerivedDirectImage U.ι).FullyFaithful := by
  let G := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let a : schemeOpenRestriction X U ⊣ G :=
    (Modules.restrictAdjunction U.ι).ofNatIsoLeft (Modules.overFunctorEquiv U).symm
  let : G.PreservesKInjectiveComplexes := a.preservesKInjectiveComplexes
  let : G.Full := (Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.full
  let : G.Faithful := (Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.faithful
  exact Functor.FullyFaithful.ofFullyFaithful G.rightDerivedFunctor

/-- The exact derived equivalence reflects invertibility of restricted maps. -/
private theorem over_restriction_map_isIso
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    {E F : schemeDerivedCategory X} (f : E ⟶ F)
    (hf : IsIso ((schemeOpenRestriction X U).mapDerivedCategory.map f)) :
    IsIso ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.map f) := by
  let r := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Modules.overEquiv U
  let : IsIso (e.functor.mapDerivedCategory.map (r.mapDerivedCategory.map f)) :=
    (NatIso.isIso_map_iff (Functor.mapDerivedCategoryCompIso r e.functor) f).mpr hf
  change IsIso (r.mapDerivedCategory.map f)
  exact isIso_of_reflects_iso _ e.functor.mapDerivedCategory

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The supported adjunction unit is invertible after restriction to U and X minus T. -/
theorem supported_open_pushforward_local_comparisons_first (X : Scheme.{u}) (U : X.Opens)
    (T : Set X) (hT : IsClosed T)
    (V : X.Opens) (hV : (V : Set X) = Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
    (∀ (adj : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
        (E : schemeDerivedCategory X),
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x))) →
      ∀ W : X.Opens, W = U ∨ W = V →
        IsIso ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) W).mapDerivedCategory.map (adj.unit.app E))) := by
  intro adj E hE W hW
  rcases hW with hW | hW
  · subst W
    let ff := open_direct_image_fullyFaithful X U
    let : (schemeDerivedDirectImage U.ι).Full := ff.full
    let : (schemeDerivedDirectImage U.ι).Faithful := ff.faithful
    have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
    exact over_restriction_map_isIso X U (adj.unit.app E)
      (isIso_of_comp_hom_eq_id _ (adj.left_triangle_components E))
  · subst W
    have hz := supported_derived_restriction_zero X T V (by rw [hV]) E hE
    have hlocal : ∀ (n : ℤ) (x : U.toScheme), U.ι x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk
          ((DerivedCategory.homologyFunctor _ n).obj
            ((schemeOpenRestriction X U).mapDerivedCategory.obj E)).val.presheaf x)) := by
      intro n x hx
      let i := restrictionHomologyStalkIso X U E n x
      exact i.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr (hE n x.val hx)
    have hs := direct_image_support U.ι T hT
      ((schemeOpenRestriction X U).mapDerivedCategory.obj E) hlocal
    have hr := supported_derived_restriction_zero X T V (by rw [hV])
      ((schemeDerivedDirectImage U.ι).obj
        ((schemeOpenRestriction X U).mapDerivedCategory.obj E)) hs
    exact IsZero.isIso hz hr _


set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Any left adjoint of derived open restriction preserves cohomological support.
Identify it with exact extension by zero and compute the interior and exterior stalks. -/
private theorem left_adjoint_support
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (T : Set X)
    (S : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X)
    (adjS : S ⊣ (schemeOpenRestriction X U).mapDerivedCategory)
    (F : schemeDerivedCategory U.toScheme)
    (hF : ∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk
        ((DerivedCategory.homologyFunctor _ n).obj F).val.presheaf x))) :
    ∀ (n : ℤ) (x : X), x ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor _ n).obj (S.obj F)).val.presheaf x)) := by
  classical
  let E := SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X.toRingedSpace) U ⋙
    PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X.toRingedSpace).obj)
  let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Modules.overEquiv U
  obtain ⟨_, _, hElim, hEcolim, ⟨adjE⟩⟩ :=
    open_restriction_adjunction_exact X.toRingedSpace U
  let : PreservesFiniteLimits E := hElim
  let : PreservesFiniteColimits E := hEcolim
  let L := e.inverse ⋙ E
  let : L.Additive := Functor.additive_of_preserves_binary_products L
  let adj : L ⊣ schemeOpenRestriction X U := e.symm.toAdjunction.comp adjE
  let adjD : L.mapDerivedCategory ⊣ (schemeOpenRestriction X U).mapDerivedCategory :=
    adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      (schemeOpenRestriction X U).rightDerivedFunctorIsoMapDerivedCategory
  let α := adjD.leftAdjointUniq adjS
  let G := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let adjR : schemeOpenRestriction X U ⊣ G :=
    (Modules.restrictAdjunction U.ι).ofNatIsoLeft (Modules.overFunctorEquiv U).symm
  let : G.Full := (Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.full
  let : G.Faithful := (Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.faithful
  have : IsIso adjR.counit := adjR.counit_isIso_of_R_fully_faithful
  have : IsIso adj.unit :=
    (Adjunction.Triple.isIso_unit_iff_isIso_counit ⟨adj, adjR⟩).mpr inferInstance
  let lr : L ⋙ (schemeOpenRestriction X U) ≅ 𝟭 _ := (asIso adj.unit).symm
  intro n x hx
  let M := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F
  let H := Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor _ x
  let ih := H.mapIso ((L.mapDerivedCategoryHomologyFunctorIso n).symm.app F)
  have hz : Subsingleton (↑(TopCat.Presheaf.stalk (L.obj M).val.presheaf x)) := by
    by_cases hxU : x ∈ U
    · let h := Modules.toPresheaf U.toScheme ⋙
        TopCat.Presheaf.stalkFunctor _ (⟨x, hxU⟩ : U.toScheme)
      let j := (h.mapIso (lr.app M)).symm ≪≫
        h.mapIso ((Modules.overFunctorEquiv U).app (L.obj M)) ≪≫
        (Modules.restrictStalkNatIso U.ι ⟨x, hxU⟩).app (L.obj M)
      exact j.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp (hF n ⟨x, hxU⟩ hx)
    · exact ModuleCat.isZero_iff_subsingleton.mp
        (moduleExtensionByZero_stalk_outside X.toRingedSpace U (e.inverse.obj M) x hxU)
  have hs := ih.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr hz
  let i := H.mapIso ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).mapIso (α.app F))
  exact i.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mp hs

/-- The supported left/right direct-image comparison is locally invertible. -/
theorem supported_open_pushforward_local_comparisons_second (X : Scheme.{u}) (U : X.Opens)
    (T : Set X) (hT : IsClosed T)
    (V : X.Opens) (hV : (V : Set X) = Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
    (∀ (adj : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
        (S : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X)
        (adjS : S ⊣ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory)
        (F : schemeDerivedCategory U.toScheme),
      (∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F).val.presheaf
            x))) →
      ∀ φ : S.obj F ⟶ (schemeDerivedDirectImage U.ι).obj F,
        adjS.unit.app F ≫ (adj.homEquiv (S.obj F) F).symm φ = 𝟙 F →
        ∀ W : X.Opens, W = U ∨ W = V →
          IsIso ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) W).mapDerivedCategory.map φ)) := by
  intro adj S adjS F hF φ hφ W hW
  rcases hW with hW | hW
  · subst W
    let ff := open_direct_image_fullyFaithful X U
    let : (schemeDerivedDirectImage U.ι).Full := ff.full
    let : (schemeDerivedDirectImage U.ι).Faithful := ff.faithful
    have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
    have : IsIso adjS.unit :=
      (Adjunction.Triple.isIso_unit_iff_isIso_counit ⟨adjS, adj⟩).mpr inferInstance
    have hi : IsIso ((adj.homEquiv (S.obj F) F).symm φ) :=
      isIso_of_hom_comp_eq_id _ hφ
    rw [adj.homEquiv_counit] at hi
    let := hi
    exact over_restriction_map_isIso X U φ
      (IsIso.of_isIso_comp_right _ (adj.counit.app F))
  · subst W
    have hs := left_adjoint_support X U T S adjS F hF
    have hz := supported_derived_restriction_zero X T V (by rw [hV]) (S.obj F) hs
    have hr := direct_image_support U.ι T hT F hF
    have hz' := supported_derived_restriction_zero X T V (by rw [hV])
      ((schemeDerivedDirectImage U.ι).obj F) hr
    exact IsZero.isIso hz hz' _

/-- The two supported comparison maps are invertible after restriction to U
and to V = X minus T; this states local comparisons, not global invertibility. -/
theorem supported_open_pushforward_local_comparisons (X : Scheme.{u}) (U : X.Opens)
    (T : Set X) (hT : IsClosed T)
    (V : X.Opens) (hV : (V : Set X) = Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
    (∀ (adj : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
        (E : schemeDerivedCategory X),
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x))) →
      ∀ W : X.Opens, W = U ∨ W = V →
        IsIso ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) W).mapDerivedCategory.map (adj.unit.app E))) ∧
    (∀ (adj : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
        (S : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X)
        (adjS : S ⊣ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory)
        (F : schemeDerivedCategory U.toScheme),
      (∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F).val.presheaf
            x))) →
      ∀ φ : S.obj F ⟶ (schemeDerivedDirectImage U.ι).obj F,
        adjS.unit.app F ≫ (adj.homEquiv (S.obj F) F).symm φ = 𝟙 F →
        ∀ W : X.Opens, W = U ∨ W = V →
          IsIso ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) W).mapDerivedCategory.map φ)) := by
  exact ⟨supported_open_pushforward_local_comparisons_first X U T hT V hV,
    supported_open_pushforward_local_comparisons_second X U T hT V hV⟩

end AlgebraicGeometry.Scheme
