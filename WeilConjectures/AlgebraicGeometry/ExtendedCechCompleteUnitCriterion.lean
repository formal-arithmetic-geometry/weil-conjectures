/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocalExtendedCechDescription
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.AlgebraicGeometry.ExtendedCechCompleteImpliesUnitIso
import WeilConjectures.AlgebraicGeometry.ExtendedCechUnitIsoImpliesComplete

/-! # Fixed objects of the augmented extended Cech completion

Source: Stacks Project, algebraization.tex, Tags 099B and 099F.
-/

@[expose] public section

universe u w

open CategoryTheory

namespace CategoryTheory

/-- Local ideal completeness is equivalent to invertibility of the actual Cech unit.
This is a criterion for a single object; it contains no assertion about maps to other
objects or about the value of completion on arbitrary objects (Stacks, Tags 099B, 099F). -/
theorem ringedExtendedCech_complete_iff_unit_isIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (hK : HasLocalExtendedCechDescription O I ι K ε)
    (E : ringedSiteDerived O) :
    IsLocallyDerivedRingedIdealComplete O I ι E ↔
      IsIso (ringedCechCompletionUnit O K ε E) := by
  constructor
  · exact ringedExtendedCech_complete_implies_unit_isIso J O I ι K ε hK E
  · exact ringedExtendedCech_unit_isIso_implies_complete J O I ι K ε hK E

end CategoryTheory
