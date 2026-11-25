/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Sheaf.RingedSheafSliceConstruction
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import all WeilConjectures.CategoryTheory.ProperBaseChange.ElementRestrictionHom

/-! Restriction of modules along one generalized section.

## References

* Stacks Project, Tag 04IE
* Stacks Project, Tag 04IF
* Stacks Project, Tag 0791
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

-- The module comparisons involve several nested element sites.
set_option maxRecDepth 4000 in
/-- Restriction along a generalized section preserves colimits and the rank-one module. -/
theorem elementSectionModuleRestriction_exists
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u))
    (V : C) (t : A.obj.obj (op V)) :
    ∃ G : ringedSiteModules.{u}
        (elementRing ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) A) ⥤
      ringedSiteModules.{u} (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over V),
      PreservesColimitsOfSize.{u, u} G ∧
      Nonempty (unit (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over V) ≅
        G.obj (unit (elementRing
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) A))) ∧
      ∀ Q : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        Nonempty (G.obj ((elementModulePullback
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) A).obj Q) ≅ Q.over V) := by
  let H := (presheafToSheaf J (Type u)).obj (yoneda.obj V)
  let b : H ⟶ A := ((sheafificationAdjunction J (Type u)).homEquiv (yoneda.obj V) A).symm
    (yonedaEquiv.symm t)
  obtain ⟨E₀, ⟨k⟩⟩ := CategoryTheory.ordinarySliceComparison R V
  let L := elementModulePullbackOver (localCoefficientRings R) b
    (presentationElementRestriction_continuous b)
  obtain ⟨E, ⟨q⟩⟩ := CategoryTheory.flattenRestrictionEquivalence R b
  obtain ⟨s⟩ := ringed_sheaf_slice_adjunction
    (localCoefficientRings (presentationElementRing R A)) (CategoryTheory.fibreSheaf b)
  have : PreservesColimitsOfSize.{u, u}
      (elementModulePullback (localCoefficientRings (presentationElementRing R A))
        (CategoryTheory.fibreSheaf b)) := by
    rw [← s.pullback_eq]
    exact s.localization_modules.leftAdjoint_preservesColimits
  let : PreservesColimitsOfSize.{u, u} (L ⋙ E.functor) :=
    preservesColimits_of_natIso q.symm
  let : PreservesColimitsOfSize.{u, u} L :=
    preservesColimits_of_reflects_of_preserves L E.functor
  let G := L ⋙ E₀.modules.inverse
  refine ⟨G, inferInstance,
    ⟨(E₀.modules.inverse.mapIso E₀.forwardUnit.symm ≪≫
      E₀.modules.unitIso.symm.app _).symm⟩, ?_⟩
  intro Q
  obtain ⟨p⟩ := presentationElementRestriction_relocalization R b
    (presentationElementRestriction_continuous b)
  exact ⟨E₀.modules.inverse.mapIso (p.app Q) ≪≫
    E₀.modules.inverse.mapIso (k.app Q).symm ≪≫ E₀.modules.unitIso.symm.app _⟩

end SheafOfModules
