/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import all WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-! # Exactness of tensoring by a pro-etale locally finite free module -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

universe v w
variable {C : Type w} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]
  {R : C} [MonObj R] [IsCommMonObj R]
attribute [local instance] Mod.isGrothendieckAbelian Abelian.hasFiniteBiproducts

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale
attribute [local instance] Sheaf.symmetricCategory

private noncomputable def pullTensorIso
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    let F := (upperStar Ab.{u + 1} g).mapMod R
    Mod.tensorLeft P ⋙ F ≅ F ⋙ Mod.tensorLeft (F.obj P) := by
  let G := upperStar Ab.{u + 1} g
  let φ := 𝟙 (G.obj R)
  let F := Mod.mapModComap (G := G) φ
  let F' := G.mapMod R
  let c : F ≅ F' := NatIso.ofComponents
    (fun M ↦ Mod.isoMk (Iso.refl _) (by simp [F, F', φ, Mod.act]))
    (fun f ↦ by ext : 1; rfl)
  have : PreservesColimitsOfShape WalkingParallelPair F := by
    dsimp [F, Mod.mapModComap]
    infer_instance
  let d := Mod.tensorLeftCompMapModComapIso φ
    (fun M N ↦ Functor.LaxBraided.braided (F := G) M N) P
  exact Functor.isoWhiskerLeft _ c.symm ≪≫ d ≪≫
    Functor.isoWhiskerRight c _ ≪≫
      Functor.isoWhiskerLeft F' (Mod.tensorLeftMapIso (c.app P))

end AlgebraicGeometry.ProEtale

namespace CategoryTheory.Limits
universe x y
end CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale
attribute [local instance] Mod.isGrothendieckAbelian

end AlgebraicGeometry.ProEtale
