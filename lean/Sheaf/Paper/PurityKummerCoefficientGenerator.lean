/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.KummerModuleCoefficients
import Sheaf.Paper.PurityFiniteModuleGenerator
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Extending an actual Kummer coefficient generator to finite modules

Source: blueprint sk-prop-a1-kummer, Coefficients; finite free presentation argument.
(blueprint: lem-pur-kummer-coefficient-generator).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

private theorem insertion_add (X : Scheme.{u}) (m : ℕ)
    (M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) (a b : M) :
    kummerCoefficientInsertion X m M (a + b) =
      kummerCoefficientInsertion X m M a + kummerCoefficientInsertion X m M b := by
  ext U x
  change ((toSheafify X.smallEtaleTopology
    ((tensorLeft (kummerRootModulePresheaf X m)).obj ((Functor.const X.Etaleᵒᵖ).obj M))).app U)
      (x ⊗ₜ (a + b)) = _
  rw [TensorProduct.tmul_add, map_add]
  rfl

private theorem insertion_map (X : Scheme.{u}) (m : ℕ)
    {M N : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))} (f : M ⟶ N) (a : M) :
    kummerCoefficientInsertion X m M a ≫ (kummerAbelianTwist X m).map f =
      kummerCoefficientInsertion X m N (f a) := by
  ext U x
  let T := kummerRootModulePresheaf X m
  let φ := (tensorLeft T).map ((Functor.const X.Etaleᵒᵖ).map f)
  have h := (sheafificationAdjunction X.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))).unit.naturality φ
  have h' := congrArg (fun t ↦ (t.app U).hom (x ⊗ₜ a)) h
  exact h'.symm

private def coefficientTau (X : Scheme.{u}) (m q : ℕ)
    (x : ((Sheaf.functorH X.smallEtaleTopology q :
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}).obj
        (X.rootsOfUnitySheaf m))) :
    forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1} ⟶
      kummerAbelianTwist X m ⋙
        (Sheaf.functorH X.smallEtaleTopology q : _ ⥤ AddCommGrpCat.{u + 1}) where
  app M := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun a ↦ Sheaf.H.map (kummerCoefficientInsertion X m M a) q x)
    (fun a b ↦ by rw [insertion_add, Sheaf.H.map_add_apply]))
  naturality M N f := by
    ext a
    change Sheaf.H.map (kummerCoefficientInsertion X m N (f a)) q x =
      Sheaf.H.map ((kummerAbelianTwist X m).map f) q
        (Sheaf.H.map (kummerCoefficientInsertion X m M a) q x)
    rw [← Sheaf.H.map_comp_apply, insertion_map]

/-- A coefficient generator extends from the residue ring to every finite module.
Source: blueprint sk-prop-a1-kummer, Coefficients; finite free presentation argument.
(blueprint: lem-pur-kummer-coefficient-generator).

Proof: coefficient insertion is additive in its coefficient by distributivity of pure
tensors. It is natural in the coefficient module by naturality of the sheafification
unit. Applying the additive cohomology functor to a fixed class x gives a natural
transformation from the underlying additive-group functor to the twisted cohomology
functor. The former preserves colimits and the latter preserves finite colimits by
hypothesis. The component at the coefficient ring is an isomorphism by hR.
The finite-module generator criterion extends this to every finite module, using finite
coproducts of the coefficient ring and a finite free kernel presentation. Invertibility
of an additive-group morphism is exactly bijectivity of its underlying function.
No choice of a basis or a new generator changes the specified class x. -/
theorem kummer_coefficient_generator_bijective (X : Scheme.{u}) (m q : ℕ) [NeZero m]
    (x : ((Sheaf.functorH X.smallEtaleTopology q :
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}).obj
        (X.rootsOfUnitySheaf m)))
    (hG : PreservesFiniteColimits
      (kummerAbelianTwist X m ⋙
        (Sheaf.functorH X.smallEtaleTopology q : _ ⥤ AddCommGrpCat.{u + 1})))
    (hR : Function.Bijective (fun a : ULift.{u + 1} (ZMod m) ↦
      Sheaf.H.map (kummerCoefficientInsertion X m (ModuleCat.of (ULift.{u + 1} (ZMod m))
        (ULift.{u + 1} (ZMod m))) a) q x))
    (M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) [Finite M] :
    Function.Bijective (fun a : M ↦
      Sheaf.H.map (kummerCoefficientInsertion X m M a) q x) := by
  let : PreservesFiniteColimits
      (kummerAbelianTwist X m ⋙
        (Sheaf.functorH X.smallEtaleTopology q : _ ⥤ AddCommGrpCat.{u + 1})) := hG
  let : PreservesColimits
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1}
      (ULift.{u + 1} (ZMod m))
  have h : IsIso ((coefficientTau X m q x).app
      (ModuleCat.of (ULift.{u + 1} (ZMod m)) (ULift.{u + 1} (ZMod m)) :
        ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hR
  have := ModuleCat.isIso_app_of_rankOne_of_finite.{u + 1, u + 2, u + 1}
    (coefficientTau X m q x) h M
  exact (ConcreteCategory.isIso_iff_bijective _).mp this

end AlgebraicGeometry.Scheme
