/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded

/-!

# Transport of the derived lower shriek along isomorphisms of schemes

Let `f : X ⟶ Y` and `f' : X' ⟶ Y'` be morphisms of schemes and `eX : X ≅ X'`, `eY : Y ≅ Y'`
isomorphisms with `f ≫ eY.hom = eX.hom ≫ f'`. A compactification `c = (X ⟶[i] Z ⟶[g] Y)` of
`f` transports to the compactification `c.transport = (X' ⟶[eX⁻¹ ≫ i] Z ⟶[g ≫ eY] Y')` of `f'`,
and the derived lower shrieks attached to them are intertwined by the pullbacks along the
isomorphisms:

`Rf'_!(c.transport) ⋙ D(eY^*) ≅ D(eX^*) ⋙ Rf_!(c)`.

This only uses that `eX` and `eY` are isomorphisms: the pullback `e^*` along an isomorphism
is the pushforward `(e⁻¹)_*`, both being left adjoint to `e_*`. Combined with the
independence of `Rf_!` of the compactification, this is what transports a Frobenius
structure through `Rf_!` when the Frobenius does not act on the chosen compactification.

## Main definitions

- `AlgebraicGeometry.Etale.upperStarInvIsoLowerStarHom`: `(e⁻¹)^* ≅ e_*` for an isomorphism
  `e` of schemes.
- `AlgebraicGeometry.Compactification.transport`: the compactification of `f'` transported
  from one of `f`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationTransportIso`:
  `Rf'_!(c.transport) ⋙ D(eY^*) ≅ D(eX^*) ⋙ Rf_!(c)`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Etale

section Iso

variable {U U' : Scheme.{u}} (e : U ≅ U')

/-- The pushforwards along an isomorphism of schemes and along its inverse form an
equivalence of the categories of étale sheaves. -/
noncomputable def lowerStarEquivalence :
    Sheaf U.smallEtaleTopology A ≌ Sheaf U'.smallEtaleTopology A :=
  CategoryTheory.Equivalence.mk (e.hom)_*[A] (e.inv)_*[A]
    ((Etale.lowerStarId A U).symm ≪≫ (Etale.lowerStarComp A e.hom e.inv (𝟙 U) (by simp)).symm)
    (Etale.lowerStarComp A e.inv e.hom (𝟙 U') (by simp) ≪≫ Etale.lowerStarId A U')

/-- The pullback along the inverse of an isomorphism `e` of schemes is the pushforward along
`e`: both are left adjoint to `(e⁻¹)_*`. -/
noncomputable def upperStarInvIsoLowerStarHom : (e.inv)^*[A] ≅ (e.hom)_*[A] :=
  (Etale.upperStarLowerStarAdjunction A e.inv).leftAdjointUniq
    (lowerStarEquivalence A e).toAdjunction

end Iso

section OpenImmersion

variable {U U' Z : Scheme.{u}} (e : U ≅ U') (j : U ⟶ Z) [IsOpenImmersion j]

/-- The extension by zero along an open immersion precomposed with an isomorphism:
`(e⁻¹ ≫ j)_! ≅ e^* ⋙ j_!`, both sides being left adjoint to `j^* ⋙ (e⁻¹)^*`. -/
noncomputable def openImmersionLowerShriekCompIso :
    (e.inv ≫ j)_!open[A] ≅ (e.hom)^*[A] ⋙ (j)_!open[A] :=
  (Etale.openImmersionLowerShriekUpperStarAdjunction A (e.inv ≫ j)).leftAdjointUniq
    (((Etale.upperStarLowerStarAdjunction A e.hom).comp
        (Etale.openImmersionLowerShriekUpperStarAdjunction A j)).ofNatIsoRight
      (Functor.isoWhiskerLeft (j)^*[A] (upperStarInvIsoLowerStarHom A e).symm ≪≫
        (Etale.upperStarComp A e.inv j).symm))

end OpenImmersion

section LowerStar

variable {Y Y' : Scheme.{u}} (e : Y ≅ Y')

/-- The derived pushforward along an isomorphism `e` of schemes followed by the pullback
along `e` is the identity: `R(e_*) ⋙ D(e^*) ≅ 𝟭`. -/
noncomputable def rightDerivedLowerStarCompMapDerivedUpperStarIso :
    R((e.hom)_*[A]) ⋙ D((e.hom)^*[A]) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorNatIso (upperStarInvIsoLowerStarHom A e).symm ≪≫
        Functor.rightDerivedFunctorIsoMapDerivedCategory _) D((e.hom)^*[A]) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Etale.upperStarComp A e.hom e.inv (𝟙 Y) (by simp)).symm ≪≫ Etale.upperStarId A Y) ≪≫
    Functor.mapDerivedCategoryIdIso _

end LowerStar

section Additive

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The derived lower shriek attached to a compactification is additive: `D(i_!)` is, and so
is `R(g_*)`, being a right adjoint. -/
instance (c : Compactification f) : Rf_!(c)[A].Additive :=
  have := c.isOpenImmersion
  have := (Etale.mapDerivedUpperStarLowerStarAdjunction A c.g).right_adjoint_additive
  inferInstance

instance [HasCompactification f] : R(f)_![A].Additive :=
  inferInstanceAs (Rf_!(HasCompactification.compactification f)[A]).Additive

end Additive

end Etale

namespace Compactification

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} (eX : X ≅ X') (eY : Y ≅ Y')
  (w : f ≫ eY.hom = eX.hom ≫ f')

/-- The compactification `X' ⟶[eX⁻¹ ≫ i] Z ⟶[g ≫ eY] Y'` of `f'` transported from a
compactification `X ⟶[i] Z ⟶[g] Y` of `f` along isomorphisms `eX : X ≅ X'`, `eY : Y ≅ Y'`
with `f ≫ eY = eX ≫ f'`. -/
@[simps]
def transport (c : Compactification f) : Compactification f' where
  Z := c.Z
  g := c.g ≫ eY.hom
  i := eX.inv ≫ c.i
  comm := by
    rw [Category.assoc, ← Category.assoc c.i, ← c.comm, w, Iso.inv_hom_id_assoc]
  isProper := by
    have := c.isProper
    infer_instance
  isOpenImmersion := by
    have := c.isOpenImmersion
    infer_instance

end Compactification

namespace Etale

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} (eX : X ≅ X') (eY : Y ≅ Y')
  (w : f ≫ eY.hom = eX.hom ≫ f') (c : Compactification f)

/-- The derived lower shriek attached to the transported compactification `c.transport` of
`f'` is intertwined with the one attached to `c` by the pullbacks along `eX` and `eY`:

`Rf'_!(c.transport) ⋙ D(eY^*) ≅ D(eX^*) ⋙ Rf_!(c)`.

It is assembled from `(eX⁻¹ ≫ i)_! ≅ eX^* ⋙ i_!`
(`Etale.openImmersionLowerShriekCompIso`), the composition isomorphism
`R((g ≫ eY)_*) ≅ R(g_*) ⋙ R(eY_*)` and `R(eY_*) ⋙ D(eY^*) ≅ 𝟭`
(`Etale.rightDerivedLowerStarCompMapDerivedUpperStarIso`). -/
noncomputable def rightDerivedLowerShriekOfCompactificationTransportIso :
    Rf_!(c.transport eX eY w)[A] ⋙ D((eY.hom)^*[A]) ≅ D((eX.hom)^*[A]) ⋙ Rf_!(c)[A] :=
  have := c.isOpenImmersion
  Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekCompIso A eX c.i) ≪≫
            Functor.mapDerivedCategoryCompIso _ _) R((c.g ≫ eY.hom)_*[A]) ≪≫
        Functor.isoWhiskerLeft _
          (Functor.rightDerivedFunctorCompIso' (c.g)_*[A] (eY.hom)_*[A]
            (Etale.lowerStarComp A c.g eY.hom)).symm) D((eY.hom)^*[A]) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompMapDerivedUpperStarIso A eY) ≪≫
        Functor.rightUnitor _))

end Etale

end AlgebraicGeometry
