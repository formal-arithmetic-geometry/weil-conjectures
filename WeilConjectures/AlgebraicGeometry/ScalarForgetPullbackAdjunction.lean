/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarAbelianExtFactorization
import WeilConjectures.AlgebraicGeometry.ScalarForgetPullbackIntegerUnit

/-! # Canonical scalar-forgetful inverse-image comparison with adjunction and unit coherence

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01F7](https://stacks.math.columbia.edu/tag/01F7)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme
open Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Sheaf.monoidalCategory

/-- Canonical scalar-forgetful inverse-image comparison with adjunction and unit coherence. -/
theorem scalar_forget_pullback_adjunction (k : Type u) [Field k]
    {X Y : Scheme.{u}} (a : Y ⟶ X) :
    let L := (Opens.map a.base).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    ∃ c : scalarInverseImage (k := k) a ⋙ scalarAbelianForget k Y ≅
        scalarAbelianForget k X ⋙ L,
      (∀ (F : KSheaf X k) (G : KSheaf Y k)
        (q : (scalarInverseImage a).obj F ⟶ G),
        (((Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).homEquiv
          _ _) (c.inv.app F ≫ (scalarAbelianForget k Y).map q) =
        (scalarAbelianForget k X).map
          ((((Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k) _ _).homEquiv
            _ _) q)) ∧
      Abelian.Ext.homEquiv₀ (scalarAbelianUnitClass k Y) ≫
          (scalarAbelianForget k Y).map (scalarInverseUnitIso a).inv ≫
          c.hom.app (𝟙_ (KSheaf X k)) =
        (((Opens.map a.base).constantSheafsheafPullbackIso AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
          isTerminalTop isTerminalTop).symm.app (AddCommGrpCat.of (ULift ℤ))).hom ≫
        L.map (Abelian.Ext.homEquiv₀ (scalarAbelianUnitClass k X)) := by
  have hi := scalarForgetPullbackComparison_isIso k a
  let c := (asIso (scalarForgetPullbackComparison k a)).symm
  refine ⟨c, ?_, ?_⟩
  · intro F G q
    exact scalarForgetPullbackComparison_adjunct k a F G q
  · change _ ≫ _ ≫ (asIso (scalarForgetPullbackComparison k a)).inv.app _ = _
    rw [← Category.assoc, scalarForgetPullbackComparison_integerUnit k a,
      Category.assoc, Category.assoc]
    have he := (asIso (scalarForgetPullbackComparison k a)).hom_inv_id_app
      (𝟙_ (KSheaf X k))
    simp only [asIso_hom] at he
    erw [he, Category.comp_id]

end AlgebraicGeometry.Scheme
