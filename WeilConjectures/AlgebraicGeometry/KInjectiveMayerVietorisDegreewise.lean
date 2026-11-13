/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
import WeilConjectures.AlgebraicGeometry.InjectiveRestrictionSurjective
import WeilConjectures.AlgebraicGeometry.OpenModuleImageGluing
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-! Degreewise exactness for the concrete Mayer--Vietoris complex.

## References

* Stacks Project, Cohomology, Tag 08BV, using Tags 01EB and 01EA.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

noncomputable section
namespace AlgebraicGeometry

private theorem schemeRestrictUnit_epi
    (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [Injective M] :
    Epi ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) := by
  have hv : Epi ((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val := by
    apply PresheafOfModules.epi_of_surjective
    intro T
    change Function.Surjective
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) T.unop)
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    exact (injective_restriction_surjective X.toRingedSpace
      (U.ι.image_preimage_le T.unop) M).1
  constructor
  intro Z g h eq
  apply SheafOfModules.hom_ext
  exact (cancel_epi ((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val).mp
    (congrArg SheafOfModules.Hom.val eq)

private theorem schemeOpenModuleUnit_epi
    (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [Injective M] :
    Epi ((schemeOpenModuleAdjunction X U).unit.app M) := by
  have := schemeRestrictUnit_epi X U M
  change Epi ((Scheme.Modules.restrictAdjunction U.ι).unit.app M ≫
    (Scheme.Modules.pushforward U.ι).map ((Scheme.Modules.overFunctorEquiv U).inv.app M))
  infer_instance

private theorem schemeOpenModuleImageRestriction_epi
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [Injective M] :
    Epi ((schemeOpenModuleImageRestriction X i).app M) := by
  have := schemeOpenModuleUnit_epi X W M
  have : Epi ((schemeOpenModuleAdjunction X U).unit.app M ≫
      (schemeOpenModuleImageRestriction X i).app M) := by
    rw [schemeOpenModuleImage_unit_restriction]
    infer_instance
  exact epi_of_epi ((schemeOpenModuleAdjunction X U).unit.app M) _

/-- The concrete Mayer--Vietoris sequence is short exact in a degree whose term is injective. -/
theorem schemeMayerVietorisComplex_degreewise_shortExact
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (n : ℤ) (hI : Injective (I.X n)) :
    ((schemeMayerVietorisComplex X U V I).map
      (HomologicalComplex.eval (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (ComplexShape.up ℤ) n)).ShortExact := by
  -- Gluing supplies the kernel and monicity without using injectivity.
  let h := schemeOpenModuleImage_isPullback X U V hcover (I.X n)
  have : Injective (I.X n) := hI
  have : Epi ((schemeOpenModuleImageRestriction X
      (homOfLE (inf_le_left : U ⊓ V ≤ U))).app (I.X n)) :=
    schemeOpenModuleImageRestriction_epi X _ (I.X n)
  -- The left summand already surjects onto the overlap; the minus sign is on the right.
  have : Epi h.shortComplex'.g := by
    have : Epi (biprod.inl ≫ h.shortComplex'.g) := by
      simpa only [CommSq.shortComplex'_g, biprod.inl_desc] using
        (inferInstance : Epi ((schemeOpenModuleImageRestriction X
          (homOfLE (inf_le_left : U ⊓ V ≤ U))).app (I.X n)))
    exact epi_of_epi biprod.inl _
  have he : h.shortComplex'.ShortExact :=
    ShortComplex.ShortExact.mk' (IsPullback.exact_shortComplex' h)
      h.mono_shortComplex'_f inferInstance
  let S := (schemeMayerVietorisComplex X U V I).map
    (HomologicalComplex.eval (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ) n)
  -- Evaluation preserves the biproduct. Check both units and both signed restrictions.
  let e : S ≅ h.shortComplex' := ShortComplex.isoMk (Iso.refl _)
    (HomologicalComplex.biprodXIso
      (schemeOpenModuleImageComplex X U I) (schemeOpenModuleImageComplex X V I) n)
    (Iso.refl _) (by
      change biprod.lift ((schemeOpenModuleAdjunction X U).unit.app (I.X n))
        ((schemeOpenModuleAdjunction X V).unit.app (I.X n)) =
          (schemeMayerVietorisF X U V I).f n ≫ _
      apply biprod.hom_ext
      · rw [biprod.lift_fst, Category.assoc]
        erw [HomologicalComplex.biprodXIso_hom_fst]
        exact (HomologicalComplex.biprod_lift_fst_f
          (schemeOpenModuleImageComplexUnit X U I) (schemeOpenModuleImageComplexUnit X V I) n).symm
      · rw [biprod.lift_snd, Category.assoc]
        erw [HomologicalComplex.biprodXIso_hom_snd]
        exact (HomologicalComplex.biprod_lift_snd_f
          (schemeOpenModuleImageComplexUnit X U I) (schemeOpenModuleImageComplexUnit X V I) n).symm)
    (by
      change _ ≫ biprod.desc
        ((schemeOpenModuleImageRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U))).app
          (I.X n))
        (-((schemeOpenModuleImageRestriction X (homOfLE (inf_le_right : U ⊓ V ≤ V))).app
          (I.X n))) = (schemeMayerVietorisG X U V I).f n ≫ 𝟙 _
      rw [Category.comp_id]
      apply (cancel_epi (HomologicalComplex.biprodXIso
        (schemeOpenModuleImageComplex X U I) (schemeOpenModuleImageComplex X V I) n).inv).mp
      rw [Iso.inv_hom_id_assoc]
      apply biprod.hom_ext'
      · rw [biprod.inl_desc, ← Category.assoc]
        erw [HomologicalComplex.inl_biprodXIso_inv
          (schemeOpenModuleImageComplex X U I) (schemeOpenModuleImageComplex X V I) n]
        exact (HomologicalComplex.biprod_inl_desc_f
          (schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_left) I)
          (-(schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_right) I)) n).symm
      · rw [biprod.inr_desc, ← Category.assoc]
        erw [HomologicalComplex.inr_biprodXIso_inv
          (schemeOpenModuleImageComplex X U I) (schemeOpenModuleImageComplex X V I) n]
        exact (HomologicalComplex.biprod_inr_desc_f
          (schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_left) I)
          (-(schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_right) I)) n).symm)
  exact ShortComplex.shortExact_of_iso e.symm he

end AlgebraicGeometry
