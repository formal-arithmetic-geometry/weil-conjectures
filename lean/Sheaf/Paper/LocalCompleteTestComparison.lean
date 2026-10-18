/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.CategoryTheory.RingedSiteCompleteElement
import Sheaf.Paper.SectionLocalizationSequence

/-!
# Compatibility of local completeness tests

Source: Stacks Project, algebraization.tex, Tags 0997 and 099C.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The sequential and sectionwise-localization definitions give the same complete test.

Source: Stacks Project, algebraization.tex, Tag 0997.
(blueprint: lem-weil-pbc-local-complete-test-comparison).
Proof: on each slice, the colimit of repeated multiplication on the free rank-one module
is the localization: a representative a at stage n maps to a/f^n. This is compatible with
restrictions and identifies the sheaf colimit with the sheafified sectionwise localization.
Slice restriction of a chosen representative computes the exact derived restriction;
use the factorization isomorphism of its induced derived functor. Apply derived internal
Hom to these two isomorphisms. Isomorphic objects vanish simultaneously.
-/
theorem isRingedSiteCompleteElement_iff_localTest
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [h : ∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U)))]
    (K : ringedSiteDerived R) (U : C) (f : R.obj.obj (op U)) :
    let : ∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) := h
    IsRingedSiteCompleteElement J R K U f ↔
      IsZero ((derivedInternalHom (J.over U) (R.over U)).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj
          (ringedSectionLocalization (R.over U) (ringedSliceSection R U f))),
          (ringedDerivedRestriction R U).obj K)) := by
  let : ∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) := h
  obtain ⟨e⟩ := sectionLocalization_sequence_iso R U f
  let F := SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U
  let eK : ringedSiteDerivedRestriction
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U K ≅
      (ringedDerivedRestriction R U).obj K :=
    (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)).symm ≪≫
      F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K)
  let eL := (DerivedCategory.singleFunctor _ 0).mapIso e
  exact ((derivedInternalHom (J.over U) (R.over U)).mapIso
    (Iso.prod eL.symm.op eK)).isZero_iff

end CategoryTheory
