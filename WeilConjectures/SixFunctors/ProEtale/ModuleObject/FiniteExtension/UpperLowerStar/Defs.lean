/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.ContinuousMap

/-!

# The pushforward `f_*` and the pullback `f^*` on module objects over `C(-, T)`

Let `T` be a commutative topological ring, with coefficient ring objects
`A_X(T) = C(-, T)` of abelian pro-étale sheaves and canonical coefficient morphisms
`η_f : A_Y(T) ⟶ f_* A_X(T)` and `α_f : f^* A_Y(T) ⟶ A_X(T)`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.ContinuousMap`). This file
defines the ordinary adjoint pair `f^* ⊣ f_*` on the categories `Mod_{A_X(T)}` of module
objects, by the "`mapMod` followed by change of scalars" recipe:

* the pushforward `f_* : Mod_{A_X(T)} ⥤ Mod_{A_Y(T)}` is `mapMod(f_*)`, which sends an
  `A_X(T)`-module to an `f_* A_X(T)`-module since `f_*` is lax monoidal, followed by restriction
  of scalars along `η_f` (`ProEtale.ContinuousMapRing.lowerStar`, notation `(f)_*⟦T⟧`). Its
  underlying sheaf is `f_* M`, with `A_Y(T)` acting through `η_f`.
* the pullback `f^* : Mod_{A_Y(T)} ⥤ Mod_{A_X(T)}` is `mapMod(f^*)`, which sends an
  `A_Y(T)`-module to an `f^* A_Y(T)`-module since `f^*` is strong monoidal, followed by
  extension of scalars along `α_f` (`ProEtale.ContinuousMapRing.upperStar`, notation
  `(f)^*⟦T⟧`). Its underlying sheaf is `A_X(T) ⊗_{f^* A_Y(T)} f^* M`, the ordinary ringed-topos
  pullback.
* the adjunction `f^* ⊣ f_*` (`ProEtale.ContinuousMapRing.upperStarLowerStarAdjunction`) is the
  composition of the lift of the monoidal adjunction `f^* ⊣ f_*` to module objects
  (`Adjunction.mapModAdjunction`) with the adjunction between extension and restriction of
  scalars along `α_f`, using that `η_f` is the mate of `α_f`.

The constructions are formal: they do not require `α_f` to be invertible, and do not use any
finiteness or completeness hypothesis on `T`.

## Main results

- `ProEtale.ContinuousMapRing.lowerStar_comp_forget`: the underlying sheaf of `f_* M` is
  `f_* M`; `ProEtale.ContinuousMapRing.preservesFiniteLimits_lowerStar`: `f_*` is left exact.
- `ProEtale.ContinuousMapRing.upperStar_comp_forget`: the underlying sheaf of `f^* M` is
  `A_X(T) ⊗_{f^* A_Y(T)} f^* M`; `ProEtale.ContinuousMapRing.preservesFiniteColimits_upperStar`:
  `f^*` is right exact, and `ProEtale.ContinuousMapRing.preservesFiniteLimits_upperStar`: `f^*`
  is left exact (assumed, see below).
- `ProEtale.ContinuousMapRing.upperStarLowerStarAdjunction`: the adjunction `f^* ⊣ f_*`.
- `ProEtale.ContinuousMapRing.linearLowerStar`: the linear pushforward
  `Mod_{f^* A_Y(T)} ⥤ Mod_{A_Y(T)}`, of which `f_*` is the composition with the restriction of
  scalars along `α_f`.
- `ProEtale.ContinuousMapRing.lowerStarComp` and `ProEtale.ContinuousMapRing.upperStarComp`: the
  composition isomorphisms `f_* ⋙ g_* ≅ (f ≫ g)_*` and `(f ≫ g)^* ≅ g^* ⋙ f^*`, the latter
  obtained from the former by uniqueness of left adjoints.

## Sorried input

- `ProEtale.ContinuousMapRing.preservesFiniteLimits_upperStar`: the pullback `f^*` on module
  objects is left exact. This is an *assumption* on the coefficients: the extension of scalars
  along `α_f` is only right exact, but for the coefficient rings of interest (`T = E` or `𝒪_E`
  for a finite extension `E` of `ℚ_ℓ`) the coefficient morphism `α_f : f^* A_Y(T) ⟶ A_X(T)` is
  an isomorphism, so that `f^*` is `mapMod(f^*)` up to restriction of scalars along `α_f⁻¹`, and
  is exact. It is what makes the derived pullback the levelwise functor `D((f)^*⟦T⟧)`, as for
  étale sheaves.
- `ProEtale.isMonoidal_lowerStarComp` (in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.UpperLowerStar.Monoidal`):
  the composition isomorphism of pushforwards of sheaves is monoidal; it enters
  `ProEtale.ContinuousMapRing.lowerStarComp`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ContinuousMapRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The pushforward -/

section LowerStar

/-- The pushforward `f_* : Mod_{A_X(T)} ⥤ Mod_{A_Y(T)}` on module objects over `C(-, T)`:
`mapMod(f_*)` followed by restriction of scalars along `η_f : A_Y(T) ⟶ f_* A_X(T)`. The
underlying sheaf of `f_* M` is `f_* M`, with `A_Y(T)` acting through `η_f`. -/
noncomputable def lowerStar :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (continuousMapRingObj T X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (continuousMapRingObj T Y) :=
  (f)_*[Ab.{u + 1}].mapMod ⋙ Mod.comap (continuousMapPushforwardHom T f)

@[inherit_doc lowerStar]
scoped notation "(" f ")_*⟦" T "⟧" => lowerStar T f

/-- The underlying sheaf of `f_* M` is `f_* M`. -/
lemma lowerStar_comp_forget :
    (f)_*⟦T⟧ ⋙ Mod.forget (continuousMapRingObj T Y) =
      Mod.forget (continuousMapRingObj T X) ⋙ (f)_*[Ab.{u + 1}] := rfl

lemma lowerStar_obj_X
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (continuousMapRingObj T X)) :
    ((f)_*⟦T⟧.obj M).X = (f)_*[Ab.{u + 1}].obj M.X := rfl

/-- The action of `A_Y(T)` on `f_* M` is `η_f` followed by the action of `f_* A_X(T)` on `f_* M`
induced by the lax monoidal structure of `f_*`. -/
lemma lowerStar_obj_smul
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (continuousMapRingObj T X)) :
    γ[continuousMapRingObj T Y,((f)_*⟦T⟧.obj M).X] =
      continuousMapPushforwardHom T f ▷ (f)_*[Ab.{u + 1}].obj M.X ≫
        Functor.LaxMonoidal.μ (f)_*[Ab.{u + 1}] (continuousMapRingObj T X) M.X ≫
          (f)_*[Ab.{u + 1}].map γ[continuousMapRingObj T X,M.X] := rfl

instance lowerStar_additive : (f)_*⟦T⟧.Additive := by
  unfold lowerStar
  infer_instance

/-- The pushforward `f_*` on module objects is left exact, since `f_*` is and finite limits of
module objects are computed on the underlying sheaves. -/
instance preservesFiniteLimits_lowerStar : PreservesFiniteLimits (f)_*⟦T⟧ := by
  unfold lowerStar
  infer_instance

end LowerStar

/-! ### The pullback -/

section UpperStar

/-- The pullback `f^* : Mod_{A_Y(T)} ⥤ Mod_{A_X(T)}` on module objects over `C(-, T)`:
`mapMod(f^*)` followed by extension of scalars along `α_f : f^* A_Y(T) ⟶ A_X(T)`. The
underlying sheaf of `f^* M` is `A_X(T) ⊗_{f^* A_Y(T)} f^* M`. -/
noncomputable def upperStar :
    Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (continuousMapRingObj T Y) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (continuousMapRingObj T X) :=
  (f)^*[Ab.{u + 1}].mapMod ⋙ Mod.extendScalars (continuousMapPullbackHom T f)

@[inherit_doc upperStar]
scoped notation "(" f ")^*⟦" T "⟧" => upperStar T f

/-- The underlying sheaf of `f^* M` is the extension of scalars `A_X(T) ⊗_{f^* A_Y(T)} f^* M` of
the `f^* A_Y(T)`-module `f^* M`. -/
lemma upperStar_comp_forget :
    (f)^*⟦T⟧ ⋙ Mod.forget (continuousMapRingObj T X) =
      (f)^*[Ab.{u + 1}].mapMod ⋙ Mod.extendScalars (continuousMapPullbackHom T f) ⋙
        Mod.forget (continuousMapRingObj T X) := rfl

lemma upperStar_obj
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (continuousMapRingObj T Y)) :
    (f)^*⟦T⟧.obj M =
      Mod.extendScalarsObj (continuousMapPullbackHom T f) ((f)^*[Ab.{u + 1}].mapMod.obj M) := rfl

instance upperStar_additive : (f)^*⟦T⟧.Additive := by
  unfold upperStar
  infer_instance

/-- The pullback `f^*` on module objects is right exact, being a composition of a left adjoint
with the exact functor `mapMod(f^*)`. Its left exactness is assumed separately
(`ProEtale.ContinuousMapRing.preservesFiniteLimits_upperStar`). -/
instance preservesFiniteColimits_upperStar : PreservesFiniteColimits (f)^*⟦T⟧ := by
  unfold upperStar
  exact comp_preservesFiniteColimits _ _

end UpperStar

/-! ### The linear pushforward and the adjunction `f^* ⊣ f_*` -/

section Adjunction

/-- The *linear* pushforward `Mod_{f^* A_Y(T)} ⥤ Mod_{A_Y(T)}` of module objects over `C(-, T)`:
`mapMod(f_*)` followed by restriction of scalars along the unit `A_Y(T) ⟶ f_* f^* A_Y(T)`. Its
underlying sheaf functor is `f_*`, and `f_*` on module objects over `A_X(T)` is its composition
with the restriction of scalars along `α_f`
(`ProEtale.ContinuousMapRing.comapPullbackHomCompIso`). It is the pushforward that enters the
exceptional operations. -/
noncomputable def linearLowerStar :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((f)^*[Ab.{u + 1}].obj (continuousMapRingObj T Y)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (continuousMapRingObj T Y) :=
  (f)_*[Ab.{u + 1}].mapMod ⋙
    Mod.comap ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom
      (continuousMapRingObj T Y))

/-- The underlying sheaf of the linear pushforward is the pushforward. -/
lemma linearLowerStar_comp_forget :
    linearLowerStar T f ⋙ Mod.forget (continuousMapRingObj T Y) =
      Mod.forget _ ⋙ (f)_*[Ab.{u + 1}] := rfl

instance linearLowerStar_additive : (linearLowerStar T f).Additive := by
  unfold linearLowerStar
  infer_instance

/-- The linear pushforward is left exact. -/
instance preservesFiniteLimits_linearLowerStar : PreservesFiniteLimits (linearLowerStar T f) := by
  unfold linearLowerStar
  infer_instance

/-- The pushforward `f_*` on module objects over `A_X(T)` is the restriction of scalars along
`α_f` followed by the linear pushforward: restricting scalars along `α_f`, then along `f_* α_f`
and the unit `A_Y(T) ⟶ f_* f^* A_Y(T)`, is restricting scalars along their composition `η_f`. -/
noncomputable def comapPullbackHomCompIso :
    Mod.comap (continuousMapPullbackHom T f) ⋙ linearLowerStar T f ≅ (f)_*⟦T⟧ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((f)_*[Ab.{u + 1}].mapModComapIso (continuousMapPullbackHom T f)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Mod.comapComp _ _).symm ≪≫
      Mod.comapIsoOfEq (unitAlgHom_comp_map_continuousMapPullbackHom T f))

/-- The adjunction `f^* ⊣ f_*` on module objects over `C(-, T)`: an `A_X(T)`-linear map
`A_X(T) ⊗_{f^* A_Y(T)} f^* M ⟶ N` is the same as an `f^* A_Y(T)`-linear map `f^* M ⟶ N`, which
is the same as an `A_Y(T)`-linear map `M ⟶ f_* N`. -/
noncomputable def upperStarLowerStarAdjunction : (f)^*⟦T⟧ ⊣ (f)_*⟦T⟧ :=
  (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction
    (continuousMapRingObj T Y)).comp
    (Mod.extendRestrictAdjunction (continuousMapPullbackHom T f))).ofNatIsoRight
    (comapPullbackHomCompIso T f)

instance : (f)_*⟦T⟧.IsRightAdjoint := (upperStarLowerStarAdjunction T f).isRightAdjoint

instance : (f)^*⟦T⟧.IsLeftAdjoint := (upperStarLowerStarAdjunction T f).isLeftAdjoint

/-- The pushforward `f_*` on module objects preserves all limits of size `0`, being a right
adjoint. -/
noncomputable instance preservesLimitsOfSize_lowerStar : PreservesLimitsOfSize.{0, 0} (f)_*⟦T⟧ :=
  (upperStarLowerStarAdjunction T f).rightAdjoint_preservesLimits

/-- The pullback `f^*` on module objects preserves all colimits of size `0`, being a left
adjoint. -/
noncomputable instance preservesColimitsOfSize_upperStar :
    PreservesColimitsOfSize.{0, 0} (f)^*⟦T⟧ :=
  (upperStarLowerStarAdjunction T f).leftAdjoint_preservesColimits

end Adjunction

/-! ### Exactness of the pullback -/

section Exact

/-- The pullback `f^*` on module objects over `C(-, T)` is left exact. See the module docstring:
this is *assumed*, and is expected only for coefficient rings such as `T = E` or `𝒪_E`. -/
instance preservesFiniteLimits_upperStar : PreservesFiniteLimits (f)^*⟦T⟧ := sorry

/-- The pullback `f^*` on module objects over `C(-, T)` is exact. -/
instance preservesHomology_upperStar : (f)^*⟦T⟧.PreservesHomology := {}

end Exact

/-! ### Composition -/

section Comp

variable {Z : Scheme.{u}} (g : Y ⟶ Z)

/-- The composition isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*` of pushforwards on module objects over
`C(-, T)`: on underlying sheaves it is the composition isomorphism `ProEtale.lowerStarComp`,
which is monoidal (`ProEtale.isMonoidal_lowerStarComp`), and the two actions of `A_Z(T)`
agree since `η_{f ≫ g}` is `η_g` followed by `g_* η_f` up to `ProEtale.lowerStarComp`
(`ProEtale.continuousMapPushforwardHom_comp`). -/
noncomputable def lowerStarComp : (f)_*⟦T⟧ ⋙ (g)_*⟦T⟧ ≅ (f ≫ g)_*⟦T⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((g)_*[Ab.{u + 1}].mapModComapIso (continuousMapPushforwardHom T f)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Mod.comapComp _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapModCompIso (f)_*[Ab.{u + 1}] (g)_*[Ab.{u + 1}]
      (ProEtale.lowerStarComp Ab.{u + 1} f g).hom (continuousMapRingObj T X)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Mod.comapComp _ _).symm ≪≫
      Mod.comapIsoOfEq (by rw [continuousMapPushforwardHom_comp, Category.assoc]))

/-- The composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*` of pullbacks on module objects over
`C(-, T)`, obtained from `ProEtale.ContinuousMapRing.lowerStarComp` by uniqueness of left
adjoints: both sides are left adjoint to `f_* ⋙ g_*`. -/
noncomputable def upperStarComp : (f ≫ g)^*⟦T⟧ ≅ (g)^*⟦T⟧ ⋙ (f)^*⟦T⟧ :=
  ((conjugateIsoEquiv (upperStarLowerStarAdjunction T (f ≫ g))
      ((upperStarLowerStarAdjunction T g).comp (upperStarLowerStarAdjunction T f))).symm
    (lowerStarComp T f g).symm).symm

end Comp

end AlgebraicGeometry.ProEtale.ContinuousMapRing
