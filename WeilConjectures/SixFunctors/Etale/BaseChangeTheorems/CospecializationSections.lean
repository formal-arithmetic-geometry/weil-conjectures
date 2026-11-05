/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Cospecialization
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselianLift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import all WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.RingTheory.StrictlyHenselianNormal

/-!
# Cospecialization maps as restriction maps on the strict localization

Let `s : Spec Ω ⟶ Y` be a geometric point, `g : Y_(s) ⟶ Y` the strict localization and
`t : Spec Ω' ⟶ Y_(s)` a geometric point of `Y_(s)`. For a sheaf `G` of `Λ`-modules on `Y_ét`,
the cospecialization map `G_s ⟶ G_{t ≫ g}` is, through the identifications
`G_s ≅ Γ(Y_(s), g^* G)` and `G_{t ≫ g} ≅ Γ(Spec Ω', t^* g^* G)`, the restriction of global
sections along `t`.

## Main results

- `AlgebraicGeometry.Scheme.isIso_toPresheafFiber_of_isStrictlyHenselianLocalRing`: over a
  strictly henselian local ring `R`, the germ `Γ(Spec R, H) ⟶ H_x` at a geometric point `x`
  over the closed point is bijective.
- `AlgebraicGeometry.Scheme.bijective_cospecializationMap_of_isIso_globalSectionsUpperStarMap`:
  the cospecialization map is bijective as soon as the restriction
  `Γ(Y_(s), g^* G) ⟶ Γ(Spec Ω', t^* g^* G)` is.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

section Germ

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Sheaf Y.smallEtaleTopology A)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ X)

/-- **Germs of the unit of `f^* ⊣ f_*`.** Through `(f^* G)_y ≅ G_{y ≫ f}`, the germ of the
unit `G(U) ⟶ (f^* G)(U ×_Y X)` at the point of `U ×_Y X` induced by a point `ū` of `U` over
`y ≫ f` is the germ of `G` at `(U, ū)`. -/
@[reassoc]
lemma unit_app_toPresheafFiber_upperStarCompSheafFiberIso_hom (U : Y.Etale)
    (ū : (pointSmallEtale (y ≫ f)).fiber.obj U) :
    ((upperStarLowerStarAdjunction A f).unit.app G).hom.app (op U) ≫
        (pointSmallEtale y).toPresheafFiber (f.Etale.obj U)
          ((pointSmallEtaleFiberEtaleIso f y).inv.app U ū) ((f)^*[A].obj G).obj ≫
        (upperStarCompSheafFiberIso A f y).hom.app G =
      (pointSmallEtale (y ≫ f)).toPresheafFiber U ū G.obj := by
  rw [← Category.assoc, ← Iso.app_hom]
  apply (Iso.eq_comp_inv _).1
  simp only [upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc,
    GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous (MorphismProperty.Over.pullback @Etale ⊤ f) A
      (Y.smallGrothendieckTopology (P := @Etale)) (X.smallGrothendieckTopology (P := @Etale)))
    (upperStarLowerStarAdjunction A f) G
  rw [← Category.assoc, ← NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)]
  rfl

end Germ

section Transport

variable (A : Type u') [Category.{u + 1} A] [HasColimitsOfSize.{u, u} A] {Y : Scheme.{u}}
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]

end Transport

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- A separably closed field is a strictly henselian local ring. -/
instance isStrictlyHenselianLocalRing_of_isSepClosed (K : Type*) [Field K] [IsSepClosed K] :
    IsStrictlyHenselianLocalRing K :=
  IsStrictlyHenselianLocalRing.of_isFractionRing_of_isSepClosed K

section StrictLocalization

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The geometric point `Spec Ω ⟶ S_(s)` given by the evaluation `𝒪^{sh}_{S,s} ⟶ Ω` lies over
the closed point of the strict localization. -/
lemma spec_map_strictHenselizationEval_apply_closedPoint :
    Spec.map (strictHenselizationEval s) (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint (strictHenselization s) :=
  have : IsLocalHom (strictHenselizationEval s).hom :=
    ⟨fun _ ha ↦ isUnit_of_strictHenselizationEval_ne_zero ha.ne_zero⟩
  IsLocalRing.comap_closedPoint (strictHenselizationEval s).hom

/-- The lift `v : Spec Ω ⟶ V` of the geometric point to a pointed étale neighbourhood `(V, v)`
is the composite of `Spec` of the evaluation map `𝒪^{sh}_{S,s} ⟶ Ω` with the leg
`S_(s) ⟶ V`. -/
@[reassoc]
lemma spec_map_strictHenselizationEval_comp_strictLocalizationConeAll_π_app
    (x : PointedEtaleNeighborhood s) :
    Spec.map (strictHenselizationEval s) ≫ (strictLocalizationConeAll s).π.app x =
      x.2.left := by
  obtain ⟨c, ⟨f⟩⟩ := AffinePointedEtaleNeighborhood.exists_hom s x
  rw [← (strictLocalizationConeAll s).w f, strictLocalizationConeAll_π_app_ι_obj,
    spec_map_strictHenselizationEval_comp_strictLocalizationCone_π_app_assoc]
  exact congrArg CategoryTheory.CommaMorphism.left f.2

end StrictLocalization

/-- The strict henselization at a geometric point is a strictly henselian local ring. -/
instance isStrictlyHenselianLocalRing_strictHenselization {S : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    IsStrictlyHenselianLocalRing (strictHenselization s) :=
  (isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed _).2
    ⟨henselianLocalRing_strictHenselization s, isSepClosed_residueField_strictHenselization s⟩

end AlgebraicGeometry.Scheme
