/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.UpperLowerStar.Defs

/-!

# Lower shriek on module objects over `ℚ̄_ℓ`

Let `ℓ` be a prime. This file defines the extension by zero along open
immersions and the lower shriek along morphisms admitting a compactification on the categories
`Mod_{ℚ̄_ℓ,X}` of module objects over `ℚ̄_ℓ,X`, from the corresponding functors on
abelian sheaves and the change of scalars along the canonical coefficient morphisms.

* For an open immersion `j : U ⟶ X`, the extension by zero `j_!` on abelian sheaves is left
  adjoint to the strong monoidal `j^*` and satisfies the projection formula
  `j_!(j^* L ⊗ M) ≅ L ⊗ j_! M` (`ProEtale.PadicAlgClRing.hasProjectionFormula_openImmersion`,
  the geometric input of this file). Hence it lifts to a *linear* extension by zero
  `Mod_{j^* ℚ̄_ℓ,X} ⥤ Mod_{ℚ̄_ℓ,X}`, sending `M` to `j_! M` with the `ℚ̄_ℓ,X`-action
  `ℚ̄_ℓ,X ⊗ j_! M ≅ j_!(j^* ℚ̄_ℓ,X ⊗ M) ⟶ j_! M`
  (`ProEtale.PadicAlgClRing.linearOpenImmersionLowerShriek`, the lift
  `Adjunction.mapModLeft` of `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`).
  The extension by zero on module objects over `ℚ̄_ℓ,U` is the restriction of scalars along
  `α_j : j^* ℚ̄_ℓ,X ⟶ ℚ̄_ℓ,U` followed by the linear extension by zero,
  ```
  j_! = (linear j_!) ∘ Res_{α_j}
  ```
  (`ProEtale.PadicAlgClRing.openImmersionLowerShriek`, notation `(j)_!open⟦ℚ̄_ℓ⟧`). Its
  underlying sheaf is `j_! M`, and it is exact. Since `α_j` is an isomorphism, `j_!` is left
  adjoint to `j^* = Ext_{α_j} ∘ mapMod(j^*)` on module objects
  (`ProEtale.PadicAlgClRing.openImmersionLowerShriekUpperStarAdjunction`): the adjunction
  `linear j_! ⊣ mapMod(j^*)` composed with `Res_{α_j} ⊣ Coext_{α_j}`, and
  `Coext_{α_j} ≅ Ext_{α_j}` for an isomorphism `α_j`.
* For a compactification `X ⟶[i] Z ⟶[g] Y` of `f : X ⟶ Y`, the lower shriek is
  `f_! := i_! ⋙ g_*` (`ProEtale.PadicAlgClRing.compactificationLowerShriek`), and for `f`
  with a chosen compactification `HasCompactification.compactification f` it is
  `ProEtale.PadicAlgClRing.lowerShriek`, notation `(f)_!⟦ℚ̄_ℓ⟧`, *definitionally* the
  composition for the chosen compactification (`ProEtale.PadicAlgClRing.lowerShriek_eq`).

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs`.

## Sorried input

* `ProEtale.PadicAlgClRing.hasProjectionFormula_openImmersion`: the projection formula for
  the extension by zero along an open immersion on abelian pro-étale sheaves, i.e. the canonical
  map `j_!(j^* L ⊗ M) ⟶ L ⊗ j_! M` is an isomorphism. Both sides are the sheaf supported on `U`
  whose restriction to `U` is `j^* L ⊗ M`, the tensor product of sheaves being computed by
  sheafification of the objectwise tensor product, which commutes with restriction to `U`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### Extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The projection formula for the extension by zero `j_!` along an open immersion on abelian
pro-étale sheaves: the canonical map `j_!(j^* L ⊗ M) ⟶ L ⊗ j_! M` is an isomorphism. See the
module docstring. -/
instance hasProjectionFormula_openImmersion :
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).HasProjectionFormula :=
  sorry

/-- The *linear* extension by zero `Mod_{j^* ℚ̄_ℓ,X} ⥤ Mod_{ℚ̄_ℓ,X}` along an open immersion
`j : U ⟶ X`: the lift of the extension by zero `j_!` on abelian sheaves to module objects
through the projection formula, sending `M` to `j_! M` with the `ℚ̄_ℓ,X`-action
`ℚ̄_ℓ,X ⊗ j_! M ≅ j_!(j^* ℚ̄_ℓ,X ⊗ M) ⟶ j_! M`. -/
noncomputable def linearOpenImmersionLowerShriek :
    Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      ((j)^*[Ab.{u + 1}].obj (padicAlgClSheaf X ℓ)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ) :=
  (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
    (padicAlgClSheaf X ℓ)

/-- The underlying sheaf of the linear extension by zero is the extension by zero. -/
lemma linearOpenImmersionLowerShriek_comp_forget :
    linearOpenImmersionLowerShriek ℓ j ⋙ Mod.forget (padicAlgClSheaf X ℓ) =
      Mod.forget _ ⋙ (j)_!open[Ab.{u + 1}] := rfl

/-- The linear extension by zero is left adjoint to the transport `mapMod(j^*)` of module
objects along the strong monoidal `j^*`. -/
noncomputable def linearOpenImmersionLowerShriekAdjunction :
    linearOpenImmersionLowerShriek ℓ j ⊣ (j)^*[Ab.{u + 1}].mapMod (R := padicAlgClSheaf X ℓ) :=
  (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeftAdjunction

instance linearOpenImmersionLowerShriek_additive : (linearOpenImmersionLowerShriek ℓ j).Additive :=
  inferInstanceAs ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
    (padicAlgClSheaf X ℓ)).Additive

/-- The extension by zero on abelian sheaves preserves finite colimits, being a left adjoint. -/
instance preservesFiniteColimits_openImmersionLowerShriek_ab :
    PreservesFiniteColimits (j)_!open[Ab.{u + 1}] :=
  have : PreservesColimitsOfSize.{0, 0} (j)_!open[Ab.{u + 1}] :=
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j
      ).leftAdjoint_preservesColimits
  inferInstance

/-- The linear extension by zero is left exact, since the extension by zero on abelian sheaves
is. -/
instance preservesFiniteLimits_linearOpenImmersionLowerShriek :
    PreservesFiniteLimits (linearOpenImmersionLowerShriek ℓ j) :=
  inferInstanceAs (PreservesFiniteLimits
    ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
      (padicAlgClSheaf X ℓ)))

/-- The linear extension by zero is right exact. -/
instance preservesFiniteColimits_linearOpenImmersionLowerShriek :
    PreservesFiniteColimits (linearOpenImmersionLowerShriek ℓ j) :=
  inferInstanceAs (PreservesFiniteColimits
    ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
      (padicAlgClSheaf X ℓ)))

/-- The extension by zero `j_! : Mod_{ℚ̄_ℓ,U} ⥤ Mod_{ℚ̄_ℓ,X}` along an open immersion
`j : U ⟶ X` on module objects over `ℚ̄_ℓ`: the restriction of scalars along
`α_j : j^* ℚ̄_ℓ,X ⟶ ℚ̄_ℓ,U` followed by the linear extension by zero. Its underlying sheaf is
the extension by zero `j_! M` of the underlying sheaf, with the `ℚ̄_ℓ,X`-action induced by the
projection formula and `α_j`. -/
noncomputable def openImmersionLowerShriek :
    Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (padicAlgClSheaf U ℓ) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ) :=
  Mod.comap (padicAlgClPullbackHom ℓ j) ⋙ linearOpenImmersionLowerShriek ℓ j

@[inherit_doc openImmersionLowerShriek]
scoped notation "(" j ")_!open⟦ℚ̄_" ℓ "⟧" => openImmersionLowerShriek ℓ j

/-- The underlying sheaf of the extension by zero on module objects is the extension by zero
of the underlying sheaf. -/
lemma openImmersionLowerShriek_comp_forget :
    (j)_!open⟦ℚ̄_ℓ⟧ ⋙ Mod.forget (padicAlgClSheaf X ℓ) =
      Mod.forget (padicAlgClSheaf U ℓ) ⋙ (j)_!open[Ab.{u + 1}] := rfl

instance openImmersionLowerShriek_additive : (j)_!open⟦ℚ̄_ℓ⟧.Additive := by
  unfold openImmersionLowerShriek
  infer_instance

/-- The extension by zero on module objects along an open immersion is left exact. -/
instance preservesFiniteLimits_openImmersionLowerShriek :
    PreservesFiniteLimits (j)_!open⟦ℚ̄_ℓ⟧ := by
  unfold openImmersionLowerShriek
  exact comp_preservesFiniteLimits _ _

/-- The extension by zero on module objects along an open immersion is right exact. -/
instance preservesFiniteColimits_openImmersionLowerShriek :
    PreservesFiniteColimits (j)_!open⟦ℚ̄_ℓ⟧ := by
  unfold openImmersionLowerShriek
  exact comp_preservesFiniteColimits _ _

/-- The extension by zero on module objects along an open immersion is exact. -/
instance preservesHomology_openImmersionLowerShriek : (j)_!open⟦ℚ̄_ℓ⟧.PreservesHomology := {}

/-- For an open immersion `j`, the pullback `j^*` on module objects is left exact: since `α_j`
is an isomorphism, the extension of scalars along it is the restriction of scalars along its
inverse, and `j^*` on module objects is `mapMod(j^*)` up to this equivalence. -/
instance preservesFiniteLimits_upperStar_of_isOpenImmersion : PreservesFiniteLimits (j)^*⟦ℚ̄_ℓ⟧ :=
  preservesFiniteLimits_of_natIso (Functor.isoWhiskerLeft
    ((j)^*[Ab.{u + 1}].mapMod (R := padicAlgClSheaf X ℓ))
    (Mod.extendScalarsIsoComapInv (padicAlgClPullbackHom ℓ j))).symm

/-- For an open immersion `j`, the pullback `j^*` on module objects is exact. -/
instance preservesHomology_upperStar_of_isOpenImmersion : (j)^*⟦ℚ̄_ℓ⟧.PreservesHomology := {}

/-- The adjunction `j_! ⊣ j^*` on module objects along an open immersion: the adjunction
`linear j_! ⊣ mapMod(j^*)` composed with the adjunction `Res_{α_j} ⊣ Coext_{α_j}`, and
`Coext_{α_j} ≅ Ext_{α_j}` since `α_j` is an isomorphism. -/
noncomputable def openImmersionLowerShriekUpperStarAdjunction : (j)_!open⟦ℚ̄_ℓ⟧ ⊣ (j)^*⟦ℚ̄_ℓ⟧ :=
  ((Mod.restrictCoextendAdjunction (padicAlgClPullbackHom ℓ j)).comp
    (linearOpenImmersionLowerShriekAdjunction ℓ j)).ofNatIsoRight
    (Functor.isoWhiskerLeft ((j)^*[Ab.{u + 1}].mapMod (R := padicAlgClSheaf X ℓ))
      (Mod.extendScalarsIsoCoextendScalars (padicAlgClPullbackHom ℓ j)).symm)

instance : (j)_!open⟦ℚ̄_ℓ⟧.IsLeftAdjoint :=
  (openImmersionLowerShriekUpperStarAdjunction ℓ j).isLeftAdjoint

end OpenImmersion

/-! ### Lower shriek along a morphism admitting a compactification -/

section Compactification

variable {X Y : Scheme.{u}}

/-- The lower shriek on module objects associated with a compactification `X ⟶[i] Z ⟶[g] Y`
of `f`: the extension by zero `i_!` followed by the pushforward `g_*`. -/
noncomputable def compactificationLowerShriek {f : X ⟶ Y} (c : Compactification f) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicAlgClSheaf Y ℓ) :=
  (c.i)_!open⟦ℚ̄_ℓ⟧ ⋙ (c.g)_*⟦ℚ̄_ℓ⟧

variable (f : X ⟶ Y) [HasCompactification f]

/-- The lower shriek `f_! : Mod_{ℚ̄_ℓ,X} ⥤ Mod_{ℚ̄_ℓ,Y}` along a morphism `f : X ⟶ Y` admitting
a compactification, on module objects over `ℚ̄_ℓ`: the composition `i_! ⋙ g_*` associated
with the chosen compactification `HasCompactification.compactification f`. -/
noncomputable def lowerShriek :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicAlgClSheaf Y ℓ) :=
  compactificationLowerShriek ℓ (HasCompactification.compactification f)

@[inherit_doc lowerShriek]
scoped notation "(" f ")_!⟦ℚ̄_" ℓ "⟧" => lowerShriek ℓ f

/-- The lower shriek `f_!` on module objects is the extension by zero along the open immersion
of the chosen compactification followed by the pushforward along its proper structure
morphism. -/
lemma lowerShriek_eq :
    (f)_!⟦ℚ̄_ℓ⟧ = ((HasCompactification.compactification f).i)_!open⟦ℚ̄_ℓ⟧ ⋙
      ((HasCompactification.compactification f).g)_*⟦ℚ̄_ℓ⟧ :=
  rfl

/-- The underlying sheaf of `f_! M` is `f_! M`. -/
lemma lowerShriek_comp_forget :
    (f)_!⟦ℚ̄_ℓ⟧ ⋙ Mod.forget (padicAlgClSheaf Y ℓ) =
      Mod.forget (padicAlgClSheaf X ℓ) ⋙ ProEtale.lowerShriek Ab.{u + 1} f := rfl

instance lowerShriek_additive : (f)_!⟦ℚ̄_ℓ⟧.Additive := by
  rw [lowerShriek_eq]
  infer_instance

/-- The lower shriek `f_!` on module objects is left exact, being the composition of the exact
extension by zero along the open immersion of the chosen compactification with the left exact
pushforward along its proper structure morphism. -/
instance preservesFiniteLimits_lowerShriek : PreservesFiniteLimits (f)_!⟦ℚ̄_ℓ⟧ := by
  rw [lowerShriek_eq]
  exact comp_preservesFiniteLimits _ _

end Compactification

end AlgebraicGeometry.ProEtale.PadicAlgClRing
