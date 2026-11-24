/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# The canonical map to the geometric stalk of a constant étale sheaf

## References

* Stacks Project, Tags 03PT, 040R and 03PQ
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The global constant section followed by its germ is an isomorphism of abelian groups
(Stacks, Tags 03PT, 040R and 03PQ). -/
theorem constantSheaf_geometricStalk_isIso (T : Scheme.{u})
    (E : AddCommGrpCat.{(max u v) + 1}) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) :
    IsIso ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj E)).app
      (op (Etale.mk (𝟙 T))) ≫
        (pointSmallEtale t).toPresheafFiber (Etale.mk (𝟙 T))
          (Over.homMk t (Category.comp_id t))
          ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{(max u v) + 1}).obj E).obj) := by
  let Φ := pointSmallEtale t
  let U : T.Etale := Etale.mk (𝟙 T)
  let x : Φ.fiber.obj U := Over.homMk t (Category.comp_id t)
  have h₁ : (Φ.presheafFiberConstIso E).inv =
      Φ.toPresheafFiber U x ((Functor.const T.Etaleᵒᵖ).obj E) := by
    have h := Φ.toPresheafFiber_presheafFiberConstIso_hom E U x
    calc
      (Φ.presheafFiberConstIso E).inv = 𝟙 _ ≫ (Φ.presheafFiberConstIso E).inv :=
        (Category.id_comp _).symm
      _ = _ := by rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hcomp : (Φ.presheafFiberConstIso E).inv ≫
      Φ.presheafFiber.map (toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj E)) =
      (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj E)).app
        (op U) ≫ Φ.toPresheafFiber U x
          ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{(max u v) + 1}).obj E).obj := by
    rw [h₁, Φ.toPresheafFiber_naturality]
    rfl
  have hi : IsIso ((Φ.presheafFiberConstIso E).inv ≫
      Φ.presheafFiber.map (toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj E))) := by
    have : T.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{(max u v) + 1} :=
      GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
    have : Limits.PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget AddCommGrpCat.{(max u v) + 1}) :=
      Limits.preservesFilteredColimitsOfSize_shrink.{u, (max u v) + 1, u, (max u v) + 1} _
    infer_instance
  rw [← hcomp]
  exact hi

end AlgebraicGeometry.Scheme
