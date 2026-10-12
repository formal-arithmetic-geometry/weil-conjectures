/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Comap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Germs of the unit of `f^* ⊣ f_*`

For a morphism of schemes `f : X ⟶ Y`, a geometric point `s` of `X` and an étale sheaf `G` on
`Y`, the unit `G ⟶ f_* f^* G` is compatible with germs: the germ at `(V, v)` of a section of `G`,
carried to `(f^* G)_s` by `AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`, is the germ at
`(V ×_Y X, (v, s))` of its image under the unit.

## Main statements

- `AlgebraicGeometry.Etale.toPresheafFiber_upperStarCompSheafFiberIso_inv_app`: the germ
  description of `(upperStarCompSheafFiberIso A f s).inv`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X)

/-- **Germs of the unit.** The germ of a section `t ∈ G(V)` at a pointed étale neighbourhood
`(V, v)` of `s ≫ f`, carried to `(f^* G)_s` by the inverse of
`AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`, is the germ of the image of `t` under
the unit `G ⟶ f_* f^* G` at the pointed étale neighbourhood `(V ×_Y X, (v, s))` of `s`. -/
@[reassoc]
lemma Etale.toPresheafFiber_upperStarCompSheafFiberIso_inv_app
    (G : Sheaf Y.smallEtaleTopology A) (V : Y.Etale)
    (v : (pointSmallEtale (s ≫ f)).fiber.obj V) :
    (pointSmallEtale (s ≫ f)).toPresheafFiber V v G.obj ≫
        (Etale.upperStarCompSheafFiberIso A f s).inv.app G =
      ((Etale.upperStarLowerStarAdjunction A f).unit.app G).hom.app (op V) ≫
        (pointSmallEtale s).toPresheafFiber (f.Etale.obj V)
          ((pointSmallEtaleFiberEtaleIso f s).inv.app V v) ((f)^*[A].obj G).obj := by
  simp only [Etale.upperStarCompSheafFiberIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Category.assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc,
    GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  have key : ((Hom.Etale f).sheafAdjunctionContinuous A Y.smallEtaleTopology
      X.smallEtaleTopology).unit.app G ≫ (f)_*[A].map
        ((Functor.sheafPullbackConstruction.sheafPullbackIso
          (MorphismProperty.Over.pullback @Etale ⊤ f) A
          (smallGrothendieckTopology (@Etale) Y) (smallGrothendieckTopology (@Etale) X)).hom.app
            G) = (Etale.upperStarLowerStarAdjunction A f).unit.app G := by
    erw [Adjunction.unit_leftAdjointUniq_hom_app]
    rfl
  rw [← Category.assoc]
  exact congrArg (· ≫ _) (congrArg (fun h ↦ h.hom.app (op V)) key)

end AlgebraicGeometry
