/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Basic

/-!

# The pushforward `f_*` and the pullback `f^*` on module objects over `ℚ̄_ℓ`

Let `ℓ` be a prime, with the coefficient ring objects `ℚ̄_ℓ,X` of abelian pro-étale sheaves,
the `ℚ̄_ℓ`-sheaves of `WeilConjectures.CategoryTheory.RingObjects.EllAdic`, and the canonical
coefficient morphisms `η_f : ℚ̄_ℓ,Y ⟶ f_* ℚ̄_ℓ,X` and `α_f : f^* ℚ̄_ℓ,Y ⟶ ℚ̄_ℓ,X`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Basic`). This file
defines the ordinary adjoint pair `f^* ⊣ f_*` on the categories `Mod_{ℚ̄_ℓ,X}` of module
objects, by the "`mapMod` followed by change of scalars" recipe, exactly as in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.UpperLowerStar.Defs`:

* the pushforward `f_* : Mod_{ℚ̄_ℓ,X} ⥤ Mod_{ℚ̄_ℓ,Y}` is `mapMod(f_*)`, which sends an
  `ℚ̄_ℓ,X`-module to an `f_* ℚ̄_ℓ,X`-module since `f_*` is lax monoidal, followed by restriction
  of scalars along `η_f` (`ProEtale.PadicAlgClRing.lowerStar`, notation `(f)_*⟦ℚ̄_ℓ⟧`). Its
  underlying sheaf is `f_* M`, with `ℚ̄_ℓ,Y` acting through `η_f`.
* the pullback `f^* : Mod_{ℚ̄_ℓ,Y} ⥤ Mod_{ℚ̄_ℓ,X}` is `mapMod(f^*)`, which sends an
  `ℚ̄_ℓ,Y`-module to an `f^* ℚ̄_ℓ,Y`-module since `f^*` is strong monoidal, followed by
  extension of scalars along `α_f` (`ProEtale.PadicAlgClRing.upperStar`, notation
  `(f)^*⟦ℚ̄_ℓ⟧`). Its underlying sheaf is `ℚ̄_ℓ,X ⊗_{f^* ℚ̄_ℓ,Y} f^* M`, the ordinary ringed-topos
  pullback.
* the adjunction `f^* ⊣ f_*` (`ProEtale.PadicAlgClRing.upperStarLowerStarAdjunction`) is the
  composition of the lift of the monoidal adjunction `f^* ⊣ f_*` to module objects
  (`Adjunction.mapModAdjunction`) with the adjunction between extension and restriction of
  scalars along `α_f`, using that `η_f` is the mate of `α_f`.

The constructions are formal: they do not require `α_f` to be invertible, and do not use the
identification `ℚ̄_ℓ,X = colim_E E_X` of `ℚ̄_ℓ,X` with the colimit of the sheaves `E_X` of the
finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`.

## Main results

- `ProEtale.PadicAlgClRing.lowerStar_comp_forget`: the underlying sheaf of `f_* M` is
  `f_* M`; `ProEtale.PadicAlgClRing.preservesFiniteLimits_lowerStar`: `f_*` is left exact.
- `ProEtale.PadicAlgClRing.upperStar_comp_forget`: the underlying sheaf of `f^* M` is
  `ℚ̄_ℓ,X ⊗_{f^* ℚ̄_ℓ,Y} f^* M`; `ProEtale.PadicAlgClRing.preservesFiniteColimits_upperStar`:
  `f^*` is right exact, and `ProEtale.PadicAlgClRing.preservesFiniteLimits_upperStar`: `f^*` is
  left exact (assumed, see below).
- `ProEtale.PadicAlgClRing.upperStarLowerStarAdjunction`: the adjunction `f^* ⊣ f_*`.
- `ProEtale.PadicAlgClRing.linearLowerStar`: the linear pushforward
  `Mod_{f^* ℚ̄_ℓ,Y} ⥤ Mod_{ℚ̄_ℓ,Y}`, of which `f_*` is the composition with the restriction of
  scalars along `α_f`.
- `ProEtale.PadicAlgClRing.lowerStarComp` and `ProEtale.PadicAlgClRing.upperStarComp`: the
  composition isomorphisms `f_* ⋙ g_* ≅ (f ≫ g)_*` and `(f ≫ g)^* ≅ g^* ⋙ f^*`, the latter
  obtained from the former by uniqueness of left adjoints.

## Sorried input

- `ProEtale.PadicAlgClRing.preservesFiniteLimits_upperStar`: the pullback `f^*` on module
  objects is left exact. This is an *assumption*: the extension of scalars along `α_f` is only
  right exact, but `α_f : f^* ℚ̄_ℓ,Y ⟶ ℚ̄_ℓ,X` is expected to be an isomorphism (`f^*` commutes
  with the colimit `ℚ̄_ℓ = colim_E E` and `α_f` is an isomorphism for each `E_X`), so that `f^*` is
  `mapMod(f^*)` up to restriction of scalars along `α_f⁻¹`, and is exact. It is what makes the
  derived pullback the levelwise functor `D((f)^*⟦ℚ̄_ℓ⟧)`, as for étale sheaves.
- `ProEtale.isMonoidal_lowerStarComp` (in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.UpperLowerStar.Monoidal`):
  the composition isomorphism of pushforwards of sheaves is monoidal; it enters
  `ProEtale.PadicAlgClRing.lowerStarComp`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The pushforward -/

section LowerStar

/-- The pushforward `f_* : Mod_{ℚ̄_ℓ,X} ⥤ Mod_{ℚ̄_ℓ,Y}` on module objects over `ℚ̄_ℓ`:
`mapMod(f_*)` followed by restriction of scalars along `η_f : ℚ̄_ℓ,Y ⟶ f_* ℚ̄_ℓ,X`. The
underlying sheaf of `f_* M` is `f_* M`, with `ℚ̄_ℓ,Y` acting through `η_f`. -/
noncomputable def lowerStar :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicAlgClSheaf Y ℓ) :=
  (f)_*[Ab.{u + 1}].mapMod ⋙ Mod.comap (padicAlgClPushforwardHom ℓ f)

@[inherit_doc lowerStar]
scoped notation "(" f ")_*⟦ℚ̄_" ℓ "⟧" => lowerStar ℓ f

/-- The underlying sheaf of `f_* M` is `f_* M`. -/
lemma lowerStar_comp_forget :
    (f)_*⟦ℚ̄_ℓ⟧ ⋙ Mod.forget (padicAlgClSheaf Y ℓ) =
      Mod.forget (padicAlgClSheaf X ℓ) ⋙ (f)_*[Ab.{u + 1}] := rfl

lemma lowerStar_obj_X
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ)) :
    ((f)_*⟦ℚ̄_ℓ⟧.obj M).X = (f)_*[Ab.{u + 1}].obj M.X := rfl

/-- The action of `ℚ̄_ℓ,Y` on `f_* M` is `η_f` followed by the action of `f_* ℚ̄_ℓ,X` on `f_* M`
induced by the lax monoidal structure of `f_*`. -/
lemma lowerStar_obj_smul
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ)) :
    γ[padicAlgClSheaf Y ℓ,((f)_*⟦ℚ̄_ℓ⟧.obj M).X] =
      padicAlgClPushforwardHom ℓ f ▷ (f)_*[Ab.{u + 1}].obj M.X ≫
        Functor.LaxMonoidal.μ (f)_*[Ab.{u + 1}] (padicAlgClSheaf X ℓ) M.X ≫
          (f)_*[Ab.{u + 1}].map γ[padicAlgClSheaf X ℓ,M.X] := rfl

instance lowerStar_additive : (f)_*⟦ℚ̄_ℓ⟧.Additive := by
  unfold lowerStar
  infer_instance

/-- The pushforward `f_*` on module objects is left exact, since `f_*` is and finite limits of
module objects are computed on the underlying sheaves. -/
instance preservesFiniteLimits_lowerStar : PreservesFiniteLimits (f)_*⟦ℚ̄_ℓ⟧ := by
  unfold lowerStar
  infer_instance

end LowerStar

/-! ### The pullback -/

section UpperStar

/-- The pullback `f^* : Mod_{ℚ̄_ℓ,Y} ⥤ Mod_{ℚ̄_ℓ,X}` on module objects over `ℚ̄_ℓ`:
`mapMod(f^*)` followed by extension of scalars along `α_f : f^* ℚ̄_ℓ,Y ⟶ ℚ̄_ℓ,X`. The
underlying sheaf of `f^* M` is `ℚ̄_ℓ,X ⊗_{f^* ℚ̄_ℓ,Y} f^* M`. -/
noncomputable def upperStar :
    Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicAlgClSheaf Y ℓ) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ) :=
  (f)^*[Ab.{u + 1}].mapMod ⋙ Mod.extendScalars (padicAlgClPullbackHom ℓ f)

@[inherit_doc upperStar]
scoped notation "(" f ")^*⟦ℚ̄_" ℓ "⟧" => upperStar ℓ f

/-- The underlying sheaf of `f^* M` is the extension of scalars `ℚ̄_ℓ,X ⊗_{f^* ℚ̄_ℓ,Y} f^* M` of
the `f^* ℚ̄_ℓ,Y`-module `f^* M`. -/
lemma upperStar_comp_forget :
    (f)^*⟦ℚ̄_ℓ⟧ ⋙ Mod.forget (padicAlgClSheaf X ℓ) =
      (f)^*[Ab.{u + 1}].mapMod ⋙ Mod.extendScalars (padicAlgClPullbackHom ℓ f) ⋙
        Mod.forget (padicAlgClSheaf X ℓ) := rfl

lemma upperStar_obj
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicAlgClSheaf Y ℓ)) :
    (f)^*⟦ℚ̄_ℓ⟧.obj M =
      Mod.extendScalarsObj (padicAlgClPullbackHom ℓ f) ((f)^*[Ab.{u + 1}].mapMod.obj M) := rfl

instance upperStar_additive : (f)^*⟦ℚ̄_ℓ⟧.Additive := by
  unfold upperStar
  infer_instance

/-- The pullback `f^*` on module objects is right exact, being a composition of a left adjoint
with the exact functor `mapMod(f^*)`. Its left exactness is assumed separately
(`ProEtale.PadicAlgClRing.preservesFiniteLimits_upperStar`). -/
instance preservesFiniteColimits_upperStar : PreservesFiniteColimits (f)^*⟦ℚ̄_ℓ⟧ := by
  unfold upperStar
  exact comp_preservesFiniteColimits _ _

end UpperStar

/-! ### The linear pushforward and the adjunction `f^* ⊣ f_*` -/

section Adjunction

/-- The *linear* pushforward `Mod_{f^* ℚ̄_ℓ,Y} ⥤ Mod_{ℚ̄_ℓ,Y}` of module objects over `ℚ̄_ℓ`:
`mapMod(f_*)` followed by restriction of scalars along the unit `ℚ̄_ℓ,Y ⟶ f_* f^* ℚ̄_ℓ,Y`. Its
underlying sheaf functor is `f_*`, and `f_*` on module objects over `ℚ̄_ℓ,X` is its composition
with the restriction of scalars along `α_f`
(`ProEtale.PadicAlgClRing.comapPullbackHomCompIso`). It is the pushforward that enters the
exceptional operations. -/
noncomputable def linearLowerStar :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((f)^*[Ab.{u + 1}].obj (padicAlgClSheaf Y ℓ)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicAlgClSheaf Y ℓ) :=
  (f)_*[Ab.{u + 1}].mapMod ⋙
    Mod.comap ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom
      (padicAlgClSheaf Y ℓ))

/-- The underlying sheaf of the linear pushforward is the pushforward. -/
lemma linearLowerStar_comp_forget :
    linearLowerStar ℓ f ⋙ Mod.forget (padicAlgClSheaf Y ℓ) =
      Mod.forget _ ⋙ (f)_*[Ab.{u + 1}] := rfl

instance linearLowerStar_additive : (linearLowerStar ℓ f).Additive := by
  unfold linearLowerStar
  infer_instance

/-- The linear pushforward is left exact. -/
instance preservesFiniteLimits_linearLowerStar : PreservesFiniteLimits (linearLowerStar ℓ f) := by
  unfold linearLowerStar
  infer_instance

/-- The pushforward `f_*` on module objects over `ℚ̄_ℓ,X` is the restriction of scalars along
`α_f` followed by the linear pushforward: restricting scalars along `α_f`, then along `f_* α_f`
and the unit `ℚ̄_ℓ,Y ⟶ f_* f^* ℚ̄_ℓ,Y`, is restricting scalars along their composition `η_f`. -/
noncomputable def comapPullbackHomCompIso :
    Mod.comap (padicAlgClPullbackHom ℓ f) ⋙ linearLowerStar ℓ f ≅ (f)_*⟦ℚ̄_ℓ⟧ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((f)_*[Ab.{u + 1}].mapModComapIso (padicAlgClPullbackHom ℓ f)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Mod.comapComp _ _).symm ≪≫
      Mod.comapIsoOfEq (unitAlgHom_comp_map_padicAlgClPullbackHom ℓ f))

/-- The adjunction `f^* ⊣ f_*` on module objects over `ℚ̄_ℓ`: an `ℚ̄_ℓ,X`-linear map
`ℚ̄_ℓ,X ⊗_{f^* ℚ̄_ℓ,Y} f^* M ⟶ N` is the same as an `f^* ℚ̄_ℓ,Y`-linear map `f^* M ⟶ N`, which
is the same as an `ℚ̄_ℓ,Y`-linear map `M ⟶ f_* N`. -/
noncomputable def upperStarLowerStarAdjunction : (f)^*⟦ℚ̄_ℓ⟧ ⊣ (f)_*⟦ℚ̄_ℓ⟧ :=
  (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction
    (padicAlgClSheaf Y ℓ)).comp
    (Mod.extendRestrictAdjunction (padicAlgClPullbackHom ℓ f))).ofNatIsoRight
    (comapPullbackHomCompIso ℓ f)

instance : (f)_*⟦ℚ̄_ℓ⟧.IsRightAdjoint := (upperStarLowerStarAdjunction ℓ f).isRightAdjoint

instance : (f)^*⟦ℚ̄_ℓ⟧.IsLeftAdjoint := (upperStarLowerStarAdjunction ℓ f).isLeftAdjoint

/-- The pushforward `f_*` on module objects preserves all limits of size `0`, being a right
adjoint. -/
noncomputable instance preservesLimitsOfSize_lowerStar : PreservesLimitsOfSize.{0, 0} (f)_*⟦ℚ̄_ℓ⟧ :=
  (upperStarLowerStarAdjunction ℓ f).rightAdjoint_preservesLimits

/-- The pullback `f^*` on module objects preserves all colimits of size `0`, being a left
adjoint. -/
noncomputable instance preservesColimitsOfSize_upperStar :
    PreservesColimitsOfSize.{0, 0} (f)^*⟦ℚ̄_ℓ⟧ :=
  (upperStarLowerStarAdjunction ℓ f).leftAdjoint_preservesColimits

end Adjunction

/-! ### Exactness of the pullback -/

section Exact

/-- The pullback `f^*` on module objects over `ℚ̄_ℓ` is left exact. See the module docstring:
this is *assumed*. -/
instance preservesFiniteLimits_upperStar : PreservesFiniteLimits (f)^*⟦ℚ̄_ℓ⟧ := sorry

/-- The pullback `f^*` on module objects over `ℚ̄_ℓ` is exact. -/
instance preservesHomology_upperStar : (f)^*⟦ℚ̄_ℓ⟧.PreservesHomology := {}

end Exact

/-! ### Composition -/

section Comp

variable {Z : Scheme.{u}} (g : Y ⟶ Z)

/-- The composition isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*` of pushforwards on module objects over
`ℚ̄_ℓ`: on underlying sheaves it is the composition isomorphism `ProEtale.lowerStarComp`, which
is monoidal (`ProEtale.isMonoidal_lowerStarComp`), and the two actions of `ℚ̄_ℓ,Z` agree since
`η_{f ≫ g}` is `η_g` followed by `g_* η_f` up to `ProEtale.lowerStarComp`
(`ProEtale.padicAlgClPushforwardHom_comp`). -/
noncomputable def lowerStarComp : (f)_*⟦ℚ̄_ℓ⟧ ⋙ (g)_*⟦ℚ̄_ℓ⟧ ≅ (f ≫ g)_*⟦ℚ̄_ℓ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((g)_*[Ab.{u + 1}].mapModComapIso (padicAlgClPushforwardHom ℓ f)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Mod.comapComp _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapModCompIso (f)_*[Ab.{u + 1}] (g)_*[Ab.{u + 1}]
      (ProEtale.lowerStarComp Ab.{u + 1} f g).hom (padicAlgClSheaf X ℓ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Mod.comapComp _ _).symm ≪≫
      Mod.comapIsoOfEq (by rw [padicAlgClPushforwardHom_comp, Category.assoc]))

/-- The composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*` of pullbacks on module objects over
`ℚ̄_ℓ`, obtained from `ProEtale.PadicAlgClRing.lowerStarComp` by uniqueness of left adjoints:
both sides are left adjoint to `f_* ⋙ g_*`. -/
noncomputable def upperStarComp : (f ≫ g)^*⟦ℚ̄_ℓ⟧ ≅ (g)^*⟦ℚ̄_ℓ⟧ ⋙ (f)^*⟦ℚ̄_ℓ⟧ :=
  ((conjugateIsoEquiv (upperStarLowerStarAdjunction ℓ (f ≫ g))
      ((upperStarLowerStarAdjunction ℓ g).comp (upperStarLowerStarAdjunction ℓ f))).symm
    (lowerStarComp ℓ f g).symm).symm

end Comp

end AlgebraicGeometry.ProEtale.PadicAlgClRing
