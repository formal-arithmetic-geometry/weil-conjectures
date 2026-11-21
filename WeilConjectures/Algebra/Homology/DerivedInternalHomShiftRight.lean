/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.Algebra.Homology.HomComplexShiftRight
import WeilConjectures.Algebra.Homology.HomComplexResolutionShiftComparison

/-! # Right-argument shift comparison for internal derived Hom
## References

* Stacks Project, Section 21.34 (Tag 0A8X) and Section 21.35 (Tag 08JA) of Cohomology on Sites
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Opposite
namespace CategoryTheory

/-- Shifting the target argument by n shifts internal Hom by n. -/
theorem derivedInternalHom_shift_right
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (P : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) (n : ℤ) :
    Nonempty (
      ((Functor.curry.obj (derivedInternalHom.{u, w} (C := C) J R)).obj (op P) ⋙
        shiftFunctor _ (n)) ≅
      (shiftFunctor _ n ⋙
        (Functor.curry.obj (derivedInternalHom.{u, w} (C := C) J R)).obj (op P))) := by
  classical
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let K := CochainComplex A ℤ
  let D := DerivedCategory A
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let Q : K ⥤ D := DerivedCategory.Q
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  have hI (M : K) : QuasiIso (η.app M) ∧ (I.obj M).IsKInjective :=
    ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩
  let H := Functor.uncurry.obj (homComplexFunctor (R := R))
  let B := (𝟭 Kᵒᵖ).prod I
  let L := Q.op.prod Q
  let F := derivedInternalHom.{u, w} (C := C) J R
  let S := shiftFunctor K n
  let T := shiftFunctor D n
  obtain ⟨e₀⟩ := derivedInternalHom_comparison J R I η hI
  obtain ⟨eH⟩ := homComplex_shift_right J R n
  obtain ⟨eI⟩ := homComplex_resolution_shift_comparison J R I η hI n
  let e : L ⋙ (F ⋙ T) ≅ L ⋙ ((𝟭 Dᵒᵖ).prod T ⋙ F) :=
    Functor.isoWhiskerRight e₀ T ≪≫
      Functor.isoWhiskerLeft (B ⋙ H) (Q.commShiftIso n).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft B eH) Q ≪≫
      eI ≪≫
      Functor.isoWhiskerLeft ((𝟭 Kᵒᵖ).prod S) e₀.symm ≪≫
      Functor.isoWhiskerRight (NatIso.prod (Iso.refl Q.op) (Q.commShiftIso n)) F
  let W := (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).op.prod
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  let e' : F ⋙ T ≅ (𝟭 Dᵒᵖ).prod T ⋙ F :=
    (Localization.fullyFaithfulWhiskeringLeft L W D).preimageIso e
  exact ⟨((Functor.curry.mapIso e').app (op P))⟩

end CategoryTheory
