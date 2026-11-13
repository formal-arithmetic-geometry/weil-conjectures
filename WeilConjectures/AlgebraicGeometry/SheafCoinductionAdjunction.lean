/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.SheafCoinductionAction
import WeilConjectures.AlgebraicGeometry.SheafCoinductionCounit

/-!
# The sheaf coinduction adjunction

## References

* [Stacks Project, Tag 0BUZ](https://stacks.math.columbia.edu/tag/0BUZ)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Restriction of scalars along the structure sheaf map has a right adjoint,
whose underlying module sheaf is internal Hom, with the multiplication action
and evaluation-at-one counit. This assertion does not require affineness. -/
theorem sheafHom_restrictScalars_adjunction
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    let A := ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj Y.ringCatSheaf
    let T := SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom
    let M := T.obj (SheafOfModules.unit A)
    let K := (SheafOfModules.homFunctor X.sheaf).obj (op M)
    ∃ H : SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} A,
      ∃ i : H ⋙ T ≅ K, ∃ adj : T ⊣ H,
        (∀ (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
          (a : A.obj.obj (op U)) (φ : (H.obj F).val.obj (op U))
          (W : Over U) (b : A.obj.obj (op W.left)),
          (((i.hom.app F).val.app (op U)).hom (a • φ)).app (op W) b =
            (((i.hom.app F).val.app (op U)).hom φ).app (op W)
              (A.obj.map W.hom.op a * b)) ∧
        (∀ (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
          (φ : (H.obj F).val.obj (op U)),
          ((adj.counit.app F).val.app (op U)).hom φ =
            ((((i.hom.app F).val.app (op U)).hom φ).app
              (op (Over.mk (𝟙 U)))) (1 : A.obj.obj (op U))) := by
  dsimp only
  obtain ⟨H, i, haction⟩ := sheafHom_restrictScalars_with_action f
  obtain ⟨e, he⟩ := sheafHom_restrictScalars_counit f H i haction
  refine ⟨H, i, Adjunction.mkOfHomEquiv e, haction, ?_⟩
  intro F U φ
  change (((e.homEquiv (H.obj F) F).symm (𝟙 (H.obj F))).val.app (op U)).hom φ = _
  simpa using he (H.obj F) F (𝟙 (H.obj F)) U φ

end AlgebraicGeometry
