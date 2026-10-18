/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.CategoryTheory.RingedDerivedRestriction
public import Sheaf.CategoryTheory.RingedSiteCompleteElement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Paper.LocalHomTowerCriterion

/-!
# Pointwise completeness under scalar restriction

Source: Stacks Project, algebraization.tex, Tags 0997 and 099C.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Restriction of scalars leaves the complete-element condition unchanged.

Source: Stacks Project, algebraization.tex, Tags 099C and 0997.
(blueprint: lem-weil-pbc-restriction-complete-element).
Proof: module sheaves on each small slice are Grothendieck abelian, so the unbounded
derived products and multiplication-tower limits exist. Restrict to the slice over U
and use Tag 0997 to replace the localization-Hom
vanishing criterion by vanishing of the derived multiplication tower. Under restriction
of scalars the abelian sheaf complexes and multiplication maps coincide. Exact scalar
restriction on derived categories is right adjoint to
derived extension
of scalars: derive the tensor/restriction adjunction using K-flat resolutions. Hence it
preserves derived products and carries the Roos triangle to the Roos triangle of the
restricted tower. The underlying complexes and the multiplication maps agree, including
restriction to the slice. Exact scalar restriction detects zero cohomology sheaves, hence
zero derived objects, since it leaves their underlying abelian sheaves unchanged. The
isomorphic derived-limit objects therefore vanish simultaneously. Apply the two tower
criteria in reverse. The section f acts through its image under the ring map.
-/
theorem restrictScalars_completeElement_iff
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R B : Sheaf J CommRingCat.{u}) (φ : R ⟶ B)
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))]
    [hR : ∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U)))]
    [hB : ∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (B.over U)))]
    (M : ringedSiteDerived B) (U : C) (f : R.obj.obj (op U)) :
    letI : ∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) := hR
    letI : ∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).over U)) := hB
    IsRingedSiteCompleteElement J R
      (DerivedCategory.Q.obj
        (((SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (DerivedCategory.Q.objPreimage M))) U f ↔
      IsRingedSiteCompleteElement J B M U (φ.hom.app (op U) f) := by
  sorry

end CategoryTheory
