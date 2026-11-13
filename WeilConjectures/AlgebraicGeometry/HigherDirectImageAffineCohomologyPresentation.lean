/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.OpenModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.HigherDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.HigherDirectImageCoefficientComparison
import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine-local presentation of ordinary higher direct images

## References

* Stacks Project, Cohomology, Tags 01E1 and 01E4.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Cohomology on inverse-image opens maps naturally to sections of ordinary higher
direct image, and these classes detect maps out of that higher direct image on the
affine basis. No compactness, separation or coproduct hypothesis is needed
(Stacks, Tags 01E1 and 01E4). -/
theorem higherDirectImage_affine_cohomology_presentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) :
    ∃ c : ∀ V : Y.Opens,
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
        RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p ⋙
          forget₂ (ModuleCat.{u}
            ((moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
              AddCommGrpCat.{u} ⟶
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p ⋙
        RingedSpace.openModuleSections Y.toRingedSpace V,
      ∀ (N : X.Modules) (Q : Y.Modules)
        (a b : ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj N ⟶ Q),
        (∀ (V : Y.Opens), IsAffineOpen V →
          (c V).app N ≫ (RingedSpace.openModuleSections Y.toRingedSpace V).map a =
            (c V).app N ≫ (RingedSpace.openModuleSections Y.toRingedSpace V).map b) →
        a = b := by
  obtain ⟨c, hc⟩ := higherDirectImage_coefficient_comparison f p
  refine ⟨c, ?_⟩
  intro N Q a b hab
  let : EnoughInjectives X.Modules := Scheme.Modules.enoughInjectives (X := X)
  let I := injectiveResolution
    (show SheafOfModules.{u} (moduleRings X.toRingedSpace) from N)
  let K := ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I.cocomplex
  let T := Scheme.Modules.sectionCohomologyTheta K p ≫
    (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map
      (I.isoRightDerivedObj (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p).inv
  have heq : T ≫ (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map a =
      T ≫ (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map b := by
    apply (PresheafOfModules.toPresheaf (moduleRings Y.toRingedSpace).obj).map_injective
    let B : {V : Y.Opens // IsAffineOpen V} → Y.Opens := Subtype.val
    have hB : TopologicalSpace.Opens.IsBasis (Set.range B) := by
      convert Y.isBasis_affineOpens using 1
      ext V
      simp [B, Scheme.affineOpens]
    apply TopCat.Sheaf.hom_ext
      (F := (Scheme.Modules.sectionCohomologyPresheaf K p).presheaf)
      (F' := ⟨Q.presheaf, Q.isSheaf⟩) hB
    intro V
    obtain ⟨e, he⟩ := hc N I V.val
    have h := hab V.val V.property
    rw [he] at h
    change (e.hom ≫
      ((PresheafOfModules.toPresheaf (moduleRings Y.toRingedSpace).obj).map T).app
        (Opposite.op V.val)) ≫
      ((PresheafOfModules.toPresheaf (moduleRings Y.toRingedSpace).obj).map
        ((SheafOfModules.forget (moduleRings Y.toRingedSpace)).map a)).app
          (Opposite.op V.val) =
      (e.hom ≫
        ((PresheafOfModules.toPresheaf (moduleRings Y.toRingedSpace).obj).map T).app
          (Opposite.op V.val)) ≫
        ((PresheafOfModules.toPresheaf (moduleRings Y.toRingedSpace).obj).map
          ((SheafOfModules.forget (moduleRings Y.toRingedSpace)).map b)).app
            (Opposite.op V.val) at h
    apply (cancel_epi e.hom).mp
    simpa only [Functor.map_comp, NatTrans.comp_app, Category.assoc] using h
  obtain ⟨d, _, hd⟩ := (higherDirectImagePresheaf f N I p).2.1 Q
    (T ≫ (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map a)
  have ha : Scheme.Modules.sectionCohomologyTheta K p ≫
      (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map
        ((I.isoRightDerivedObj (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p).inv ≫
          a) = T ≫ (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map a := by
    simp [T]
  have hb : Scheme.Modules.sectionCohomologyTheta K p ≫
      (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map
        ((I.isoRightDerivedObj (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p).inv ≫
          b) = T ≫ (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map a := by
    simpa only [T, Functor.map_comp, Category.assoc] using heq.symm
  exact (hd a ha).trans (hd b hb).symm

end AlgebraicGeometry
