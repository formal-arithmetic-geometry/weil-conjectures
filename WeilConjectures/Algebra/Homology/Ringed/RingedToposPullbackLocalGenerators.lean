/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ProperBaseChange.OrdinaryRingedToposPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.Algebra.Homology.ProperBaseChange.ElementSectionModuleRestriction
import WeilConjectures.Algebra.Homology.ProperBaseChange.RepresentableSliceModulePullback

/-! # Transport of a local finite generating family along a generalized section

A finite generating family of a module sheaf on a localization transports to the pullback
module along a generalized section of the inverse image of the localization.

## References

* Stacks Project, Modules on Sites, Tags 03DO (5), 03DF, and 04IF.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite

namespace SheafOfModules

/-- A section of the inverse image of a represented localization transports generators. -/
theorem ordinaryRingedToposPullback_localGenerators
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse B RI)
    (c : RI ⟶ A)
    (hc : I.ringUnderlying.hom ≫ (sheafCompose J (CategoryTheory.forget CommRingCat)).map c =
      f.ringMap)
    (M : ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (U : D) (σ : (M.over U).GeneratingSections) [σ.IsFiniteType]
    (V : C)
    (t : (f.inverse.obj ((presheafToSheaf K (Type u)).obj (yoneda.obj U))).obj.obj (op V)) :
    ∃ τ : ((ordinaryRingedToposPullback I c M).over V).GeneratingSections,
      τ.IsFiniteType := by
  obtain ⟨F, hF, ⟨eF⟩, hFM⟩ :=
    representableSliceModulePullback_exists A B f RI I c hc U
  let := hF
  let σF := σ.map F eF
  obtain ⟨G, hG, ⟨eG⟩, hGQ⟩ := elementSectionModuleRestriction_exists
    A
    (f.inverse.obj ((presheafToSheaf K (Type u)).obj (yoneda.obj U))) V t
  let := hG
  let σG := σF.map G eG
  obtain ⟨α⟩ := hFM M
  obtain ⟨β⟩ := hGQ (ordinaryRingedToposPullback I c M)
  let γ := G.mapIso α ≪≫ β
  exact ⟨σG.ofEpi γ.hom, inferInstance⟩

end SheafOfModules
