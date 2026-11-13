/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk

/-! # Natural intermediate stalk tensor comparisons

## References

* [Stacks Project, Tag 008H](https://stacks.math.columbia.edu/tag/008H)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 008B](https://stacks.math.columbia.edu/tag/008B)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory TensorProduct
namespace AlgebraicGeometry
/-- Natural stalk comparison after restricting the target to an open. -/
theorem exists_restricted_tensorPullback_stalk
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) (V : Z.Opens) (z : V.toScheme) :
    let S := (Y.presheaf.stalk (i z.1) : Type u)
    let R := (V.toScheme.presheaf.stalk z : Type u)
    let φ : S →+* R := (i.stalkMap z.1 ≫ V.ι.stalkMap z).hom
    letI : Algebra S R := φ.toAlgebra
    ∃ β : ∀ (F : Y.Modules),
      ((Scheme.Modules.restrictFunctor V.ι).obj
        ((Scheme.Modules.tensorPullback i).obj F)).presheaf.stalk z ≃+
          R ⊗[S] F.presheaf.stalk (i z.1),
      ∀ (F G : Y.Modules) (c : F ⟶ G) (x),
        β G (((Scheme.Modules.restrictFunctor V.ι).map
          ((Scheme.Modules.tensorPullback i).map c)).stalkLinearMap z x) =
        (c.stalkLinearMap (i z.1)).baseChange R (β F x)  := by
  classical
  dsimp only
  obtain ⟨e, _⟩ := Scheme.Modules.exists_tensorPullback_stalk_iso (V.ι ≫ i) z
  simp only [Scheme.Hom.stalkMap_comp] at e
  let a : Scheme.Modules.tensorPullback i ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      Scheme.Modules.tensorPullback (V.ι ≫ i) :=
    Functor.isoWhiskerLeft (Scheme.Modules.tensorPullback i)
      ((Scheme.Modules.restrictAdjunction V.ι).leftAdjointUniq
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction V.ι))) ≪≫
      (Classical.choice (Scheme.Modules.nonempty_tensorPullbackComp V.ι i)).symm
  let b := Functor.isoWhiskerRight a
    (RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace z) ≪≫ e
  refine ⟨fun F ↦ (b.app F).toLinearEquiv.toAddEquiv, ?_⟩
  intro F G c x
  have h := congrArg (fun t ↦ t x) (b.hom.naturality c)
  exact h
end AlgebraicGeometry
