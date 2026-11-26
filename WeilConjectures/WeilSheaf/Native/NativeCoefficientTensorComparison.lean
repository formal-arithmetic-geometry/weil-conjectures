/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.AlgebraicGeometry.Native.NativeModuleConstructibilityComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorIdentification
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgettingMonoidal
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal

/-! # Coefficient transport of the ordinary relative derived tensor

The coefficient equivalence carries the ordinary product-total derived tensor to the
condensed-module derived tensor.

## Implementation details

The natural ordinary Hom representatives determine the right adjoint of the standard derived
tensor, so uniqueness of left adjoints identifies the specified source tensor with the standard
derived module tensor. Scalar forgetting followed by restriction along the coefficient ring
isomorphism is an additive exact monoidal equivalence, so the generic derived monoidal
comparison (built on K-flat resolutions) is invertible for it. The native derived braiding
changes the fixed-right source convention to the fixed-left target convention.

## References

* Stacks Project, Tags 06YS and 08J9
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Opposite WeilConjectures

namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- The coefficient equivalence carries ordinary product-total derived tensor to
condensed-module derived tensor. The source tensor is fixed by its K-flat model,
including the reversed input convention of `ordinaryTensorBifunctor`. -/
theorem nativeCoefficient_tensorComparison (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
        DerivedCategory (ProEtale.AdicSheaf l Y))
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (S : CoefficientClosedStructure H)
    (β : @SymmetricCategory _ _ S.monoidal)
    (_hModels : NativeOrdinaryTensorModels l Y H R S β) :
    let F := (ProEtale.AdicSheaf.forgetAb l Y ⋙
      Mod.comap (ProEtale.nativeModuleCoefficientIso l Y).hom).mapDerivedCategory
    ∀ P : DerivedCategory (ProEtale.AdicSheaf l Y),
      Nonempty (@MonoidalCategory.tensorRight _ _ S.monoidal P ⋙ F ≅
        F ⋙ (ProEtale.CondensedRing.derivedTensor
          (Profinite.padicAlgClRingObj l) Y).obj (F.obj P)) := by
  classical
  let U := ProEtale.AdicSheaf.forgetAb l Y
  let V := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (ProEtale.nativeModuleCoefficientIso l Y).hom
  obtain ⟨c⟩ := ProEtale.nativeScalarForgetting_monoidal l Y
  let : U.Monoidal := c
  have : U.IsEquivalence := ProEtale.nativeScalarForgetting_isEquivalence l Y
  have : V.IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso
      (ProEtale.nativeModuleCoefficientIso l Y).hom).isEquivalence_functor
  let E := U ⋙ V
  let : E.Monoidal := inferInstanceAs (U ⋙ V).Monoidal
  have : E.IsEquivalence := inferInstance
  have : E.PreservesFlat := Functor.preservesFlat_of_isEquivalence E
  intro _F P
  obtain ⟨e⟩ := nativeOrdinary_tensorRight_iso l Y H R S P
  let : BraidedCategory (DerivedCategory (ProEtale.AdicSheaf l Y)) :=
    (DerivedCategory.nonempty_braidedCategory (ProEtale.AdicSheaf l Y)).some
  exact ⟨Functor.isoWhiskerRight
      (e ≪≫ (BraidedCategory.tensorLeftIsoTensorRight P).symm) E.mapDerivedCategory ≪≫
    asIso (E.mapDerivedCategoryTensorComparison.app P)⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
