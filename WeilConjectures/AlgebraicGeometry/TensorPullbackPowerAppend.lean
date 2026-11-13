/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
import all WeilConjectures.AlgebraicGeometry.BoundaryCoefficientDegreeSplit

/-! # Pullback of tensor-power concatenation with one factor

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] tensorPullback boundaryPullbackComparison

/-- The recursive pullback comparison preserves appending a single tensor factor.
This has no block size, coefficient object, section, ideal, or square-zero hypothesis. -/
theorem boundaryPullbackPowIso_append {X Z : Scheme.{u}} (j : Z ⟶ X)
    (B : X.Modules) (e : ℕ) :
    (boundaryPullbackTensorIso j (B.tensorPow e) B).inv ≫
        (tensorPullback j).map
          ((B.tensorPow e ◁ (ρ_ B).inv) ≫ (B.tensorPowAddIso e 1).inv) ≫
        (boundaryPullbackPowIso j B (e + 1)).hom =
      (boundaryPullbackPowIso j B e).hom ▷ (tensorPullback j).obj B ≫
        (((tensorPullback j).obj B).tensorPow e ◁ (ρ_ ((tensorPullback j).obj B)).inv) ≫
        (((tensorPullback j).obj B).tensorPowAddIso e 1).inv := by
  let : (tensorPullback j).Monoidal :=
    Functor.Monoidal.transport (boundaryPullbackComparison j).symm
  have hT (A C : X.Modules) : (boundaryPullbackTensorIso j A C).inv =
      Functor.LaxMonoidal.μ (tensorPullback j) A C := rfl
  have he : (pullbackObjUnitIso j).inv = Functor.LaxMonoidal.ε (pullback j) := by
    apply (cancel_mono (pullbackObjUnitIso j).hom).mp
    rw [Iso.inv_hom_id, ← pullback_monoidal_unit_comparison j]
    exact (Functor.Monoidal.ε_η (pullback j)).symm
  have h0 : (boundaryPullbackPowIso j B 0).inv =
      Functor.LaxMonoidal.ε (tensorPullback j) := by
    change (pullbackObjUnitIso j).inv ≫ (boundaryPullbackComparison j).inv.app _ =
      Functor.LaxMonoidal.ε (pullback j) ≫ (boundaryPullbackComparison j).inv.app _
    rw [he]
    rfl
  have h1 : (ρ_ ((tensorPullback j).obj B)).inv ≫
      (boundaryPullbackPowIso j B 1).inv = (tensorPullback j).map (ρ_ B).inv := by
    simp only [boundaryPullbackPowIso, Iso.trans_inv, tensorIso_inv, Iso.refl_inv,
      id_tensorHom]
    change (ρ_ ((tensorPullback j).obj B)).inv ≫
      (tensorPullback j).obj B ◁ (boundaryPullbackPowIso j B 0).inv ≫
      (boundaryPullbackTensorIso j B (𝟙_ X.Modules)).inv = _
    rw [h0, hT]
    apply (cancel_mono ((tensorPullback j).map (ρ_ B).hom)).mp
    simp only [tensorPow_zero, Category.assoc]
    erw [← Functor.LaxMonoidal.right_unitality (tensorPullback j) B]
    rw [Iso.inv_hom_id, ← Functor.map_comp, Iso.inv_hom_id, (tensorPullback j).map_id]
  have hh := pullback_power_add j B e 1
  apply (cancel_epi ((boundaryPullbackPowIso j B e).inv ▷ (tensorPullback j).obj B)).mp
  simp only [inv_hom_whiskerRight_assoc]
  rw [hT, Functor.map_comp]
  simp only [Category.assoc, tensorPow_succ, tensorPow_zero] at hh ⊢
  erw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [← Category.assoc, ← Category.assoc]
  have ht : (boundaryPullbackPowIso j B e).inv ▷ (tensorPullback j).obj B ≫
      (tensorPullback j).obj (B.tensorPow e) ◁ (tensorPullback j).map (ρ_ B).inv =
      (((tensorPullback j).obj B).tensorPow e ◁ (ρ_ ((tensorPullback j).obj B)).inv) ≫
        ((boundaryPullbackPowIso j B e).inv ⊗ₘ
          (boundaryPullbackPowIso j B 1).inv) := by
    rw [← h1]
    simp only [whiskerLeft_comp, tensorHom_def]
    erw [whisker_exchange_assoc]
  rw [ht]
  simp only [Category.assoc]
  rw [← hT, reassoc_of% hh, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules
