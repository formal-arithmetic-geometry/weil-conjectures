/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.CategoryTheory.RingedSiteCompleteElement
public import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.CategoryTheory.RingedSiteLocalizationRestriction

/-! Restriction comparison for the localization-Hom vanishing criterion. -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace CategoryTheory

/-- Restriction of the localization-Hom object to a further slice.

Source: Stacks Project, sites-cohomology.tex, Tag 08JB, and algebraization.tex,
Tags 0996 and 0998. (blueprint: lem-weil-pbc-ringed-complete-element-restriction).

Proof: Restriction to a slice is exact and preserves colimits. Apply it to the
sequential diagram O_U --f--> O_U --f--> ... defining the coefficient localization.
The restricted unit module is O_V, and its endomorphism is multiplication by f|V,
so the colimit comparison identifies the restricted localization with O_V[1/(f|V)].
The canonical composition of exact restriction functors identifies (K|U)|V with
K|V. The existing derived internal-Hom restriction isomorphism (Tag 08JB) and
these two comparisons give the displayed isomorphism. The chosen representative
definition of derived restriction is identified with the induced exact functor
using its factorization through Q and Q.objObjPreimageIso. There is no condition
on boundedness or on the section, and the argument applies to f = 0 as well.
-/
theorem ringedSite_complete_element_restriction
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) (U V : C) (a : V ⟶ U)
    (f : R.obj.obj (op U)) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
    let : ∀ W : C, HasDerivedCategory.{w} (SheafOfModules.{u}
        ((sheafCompose (J.over W) (forget₂ CommRingCat RingCat)).obj (R.over W))) :=
      fun W ↦ inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (R₀.over W)))
    Nonempty (((SheafOfModules.overMap.{u} R₀ a).mapDerivedCategory).obj
      ((derivedInternalHom (J.over U) (R.over U)).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj (ringedSiteSectionLocalization R₀ U f)),
          ringedSiteDerivedRestriction R₀ U K)) ≅
      (derivedInternalHom (J.over V) (R.over V)).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj
          (ringedSiteSectionLocalization R₀ V (R.obj.map a.op f))),
          ringedSiteDerivedRestriction R₀ V K)) := by
  let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let : ∀ W : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over W) (forget₂ CommRingCat RingCat)).obj (R.over W))) :=
    fun W ↦ inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (R₀.over W)))
  let F := SheafOfModules.overMap.{u} R₀ a
  let G := SheafOfModules.overFunctor.{u} R₀ U
  let G' := SheafOfModules.overFunctor.{u} R₀ V
  let P := DerivedCategory.Q.objPreimage K
  have hU : ringedSiteDerivedRestriction R₀ U K ≅ G.mapDerivedCategory.obj K :=
    (G.mapDerivedCategoryFactors.app P).symm ≪≫
      G.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K)
  have hV : ringedSiteDerivedRestriction R₀ V K ≅ G'.mapDerivedCategory.obj K :=
    (G'.mapDerivedCategoryFactors.app P).symm ≪≫
      G'.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K)
  let c := (Functor.mapDerivedCategoryCompIso G F).symm ≪≫
    Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap R₀ a)
  have hK : F.mapDerivedCategory.obj (ringedSiteDerivedRestriction R₀ U K) ≅
      ringedSiteDerivedRestriction R₀ V K :=
    F.mapDerivedCategory.mapIso hU ≪≫ c.app K ≪≫ hV.symm
  obtain ⟨l⟩ := ringedSite_localization_restriction J R U V a f
  have hL : F.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj (ringedSiteSectionLocalization R₀ U f)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ringedSiteSectionLocalization R₀ V (R.obj.map a.op f)) :=
    (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso l
  obtain ⟨_, s, _⟩ := ringedInternalHom_restriction J R
  exact ⟨(s U V a).app _ ≪≫
    (derivedInternalHom (J.over V) (R.over V)).mapIso
      (Iso.prod hL.symm.op hK)⟩

end CategoryTheory
