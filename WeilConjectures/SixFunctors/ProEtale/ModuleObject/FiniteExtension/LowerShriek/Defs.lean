/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.UpperLowerStar.Defs

/-!

# Lower shriek on module objects over `C(-, T)`

Let `T` be a commutative topological ring. This file defines the extension by zero along open
immersions and the lower shriek along morphisms admitting a compactification on the categories
`Mod_{A_X(T)}` of module objects over `A_X(T) = C(-, T)`, from the corresponding functors on
abelian sheaves and the change of scalars along the canonical coefficient morphisms.

* For an open immersion `j : U ⟶ X`, the extension by zero `j_!` on abelian sheaves is left
  adjoint to the strong monoidal `j^*` and satisfies the projection formula
  `j_!(j^* L ⊗ M) ≅ L ⊗ j_! M` (`ProEtale.ContinuousMapRing.hasProjectionFormula_openImmersion`,
  the geometric input of this file). Hence it lifts to a *linear* extension by zero
  `Mod_{j^* A_X(T)} ⥤ Mod_{A_X(T)}`, sending `M` to `j_! M` with the `A_X(T)`-action
  `A_X(T) ⊗ j_! M ≅ j_!(j^* A_X(T) ⊗ M) ⟶ j_! M`
  (`ProEtale.ContinuousMapRing.linearOpenImmersionLowerShriek`, the lift
  `Adjunction.mapModLeft` of `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`).
  The extension by zero on module objects over `A_U(T)` is the restriction of scalars along
  `α_j : j^* A_X(T) ⟶ A_U(T)` followed by the linear extension by zero,
  ```
  j_! = (linear j_!) ∘ Res_{α_j}
  ```
  (`ProEtale.ContinuousMapRing.openImmersionLowerShriek`, notation `(j)_!open⟦T⟧`). Its
  underlying sheaf is `j_! M`, and it is exact. Since `α_j` is an isomorphism, `j_!` is left
  adjoint to `j^* = Ext_{α_j} ∘ mapMod(j^*)` on module objects
  (`ProEtale.ContinuousMapRing.openImmersionLowerShriekUpperStarAdjunction`): the adjunction
  `linear j_! ⊣ mapMod(j^*)` composed with `Res_{α_j} ⊣ Coext_{α_j}`, and
  `Coext_{α_j} ≅ Ext_{α_j}` for an isomorphism `α_j`.
* For a compactification `X ⟶[i] Z ⟶[g] Y` of `f : X ⟶ Y`, the lower shriek is
  `f_! := i_! ⋙ g_*` (`ProEtale.ContinuousMapRing.compactificationLowerShriek`), and for `f`
  with a chosen compactification `HasCompactification.compactification f` it is
  `ProEtale.ContinuousMapRing.lowerShriek`, notation `(f)_!⟦T⟧`, *definitionally* the
  composition for the chosen compactification (`ProEtale.ContinuousMapRing.lowerShriek_eq`).

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs`.

## Sorried input

* `ProEtale.ContinuousMapRing.hasProjectionFormula_openImmersion`: the projection formula for
  the extension by zero along an open immersion on abelian pro-étale sheaves, i.e. the canonical
  map `j_!(j^* L ⊗ M) ⟶ L ⊗ j_! M` is an isomorphism. Both sides are the sheaf supported on `U`
  whose restriction to `U` is `j^* L ⊗ M`, the tensor product of sheaves being computed by
  sheafification of the objectwise tensor product, which commutes with restriction to `U`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ContinuousMapRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-! ### Extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The projection formula for the extension by zero `j_!` along an open immersion on abelian
pro-étale sheaves: the canonical map `j_!(j^* L ⊗ M) ⟶ L ⊗ j_! M` is an isomorphism. See the
module docstring. -/
instance hasProjectionFormula_openImmersion :
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).HasProjectionFormula :=
  sorry

/-- The *linear* extension by zero `Mod_{j^* A_X(T)} ⥤ Mod_{A_X(T)}` along an open immersion
`j : U ⟶ X`: the lift of the extension by zero `j_!` on abelian sheaves to module objects
through the projection formula, sending `M` to `j_! M` with the `A_X(T)`-action
`A_X(T) ⊗ j_! M ≅ j_!(j^* A_X(T) ⊗ M) ⟶ j_! M`. -/
noncomputable def linearOpenImmersionLowerShriek :
    Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      ((j)^*[Ab.{u + 1}].obj (continuousMapRingObj T X)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (continuousMapRingObj T X) :=
  (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
    (continuousMapRingObj T X)

/-- The underlying sheaf of the linear extension by zero is the extension by zero. -/
lemma linearOpenImmersionLowerShriek_comp_forget :
    linearOpenImmersionLowerShriek T j ⋙ Mod.forget (continuousMapRingObj T X) =
      Mod.forget _ ⋙ (j)_!open[Ab.{u + 1}] := rfl

/-- The linear extension by zero is left adjoint to the transport `mapMod(j^*)` of module
objects along the strong monoidal `j^*`. -/
noncomputable def linearOpenImmersionLowerShriekAdjunction :
    linearOpenImmersionLowerShriek T j ⊣ (j)^*[Ab.{u + 1}].mapMod (R := continuousMapRingObj T X) :=
  (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeftAdjunction

instance linearOpenImmersionLowerShriek_additive : (linearOpenImmersionLowerShriek T j).Additive :=
  inferInstanceAs ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
    (continuousMapRingObj T X)).Additive

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
    PreservesFiniteLimits (linearOpenImmersionLowerShriek T j) :=
  inferInstanceAs (PreservesFiniteLimits
    ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
      (continuousMapRingObj T X)))

/-- The linear extension by zero is right exact. -/
instance preservesFiniteColimits_linearOpenImmersionLowerShriek :
    PreservesFiniteColimits (linearOpenImmersionLowerShriek T j) :=
  inferInstanceAs (PreservesFiniteColimits
    ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
      (continuousMapRingObj T X)))

/-- The extension by zero `j_! : Mod_{A_U(T)} ⥤ Mod_{A_X(T)}` along an open immersion
`j : U ⟶ X` on module objects over `C(-, T)`: the restriction of scalars along
`α_j : j^* A_X(T) ⟶ A_U(T)` followed by the linear extension by zero. Its underlying sheaf is
the extension by zero `j_! M` of the underlying sheaf, with the `A_X(T)`-action induced by the
projection formula and `α_j`. -/
noncomputable def openImmersionLowerShriek :
    Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (continuousMapRingObj T U) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (continuousMapRingObj T X) :=
  Mod.comap (continuousMapPullbackHom T j) ⋙ linearOpenImmersionLowerShriek T j

@[inherit_doc openImmersionLowerShriek]
scoped notation "(" j ")_!open⟦" T "⟧" => openImmersionLowerShriek T j

/-- The underlying sheaf of the extension by zero on module objects is the extension by zero
of the underlying sheaf. -/
lemma openImmersionLowerShriek_comp_forget :
    (j)_!open⟦T⟧ ⋙ Mod.forget (continuousMapRingObj T X) =
      Mod.forget (continuousMapRingObj T U) ⋙ (j)_!open[Ab.{u + 1}] := rfl

instance openImmersionLowerShriek_additive : (j)_!open⟦T⟧.Additive := by
  unfold openImmersionLowerShriek
  infer_instance

/-- The extension by zero on module objects along an open immersion is left exact. -/
instance preservesFiniteLimits_openImmersionLowerShriek :
    PreservesFiniteLimits (j)_!open⟦T⟧ := by
  unfold openImmersionLowerShriek
  exact comp_preservesFiniteLimits _ _

/-- The extension by zero on module objects along an open immersion is right exact. -/
instance preservesFiniteColimits_openImmersionLowerShriek :
    PreservesFiniteColimits (j)_!open⟦T⟧ := by
  unfold openImmersionLowerShriek
  exact comp_preservesFiniteColimits _ _

/-- The extension by zero on module objects along an open immersion is exact. -/
instance preservesHomology_openImmersionLowerShriek : (j)_!open⟦T⟧.PreservesHomology := {}

/-- For an open immersion `j`, the pullback `j^*` on module objects is left exact: since `α_j`
is an isomorphism, the extension of scalars along it is the restriction of scalars along its
inverse, and `j^*` on module objects is `mapMod(j^*)` up to this equivalence. -/
instance preservesFiniteLimits_upperStar_of_isOpenImmersion : PreservesFiniteLimits (j)^*⟦T⟧ :=
  preservesFiniteLimits_of_natIso (Functor.isoWhiskerLeft
    ((j)^*[Ab.{u + 1}].mapMod (R := continuousMapRingObj T X))
    (Mod.extendScalarsIsoComapInv (continuousMapPullbackHom T j))).symm

/-- For an open immersion `j`, the pullback `j^*` on module objects is exact. -/
instance preservesHomology_upperStar_of_isOpenImmersion : (j)^*⟦T⟧.PreservesHomology := {}

/-- The adjunction `j_! ⊣ j^*` on module objects along an open immersion: the adjunction
`linear j_! ⊣ mapMod(j^*)` composed with the adjunction `Res_{α_j} ⊣ Coext_{α_j}`, and
`Coext_{α_j} ≅ Ext_{α_j}` since `α_j` is an isomorphism. -/
noncomputable def openImmersionLowerShriekUpperStarAdjunction : (j)_!open⟦T⟧ ⊣ (j)^*⟦T⟧ :=
  ((Mod.restrictCoextendAdjunction (continuousMapPullbackHom T j)).comp
    (linearOpenImmersionLowerShriekAdjunction T j)).ofNatIsoRight
    (Functor.isoWhiskerLeft ((j)^*[Ab.{u + 1}].mapMod (R := continuousMapRingObj T X))
      (Mod.extendScalarsIsoCoextendScalars (continuousMapPullbackHom T j)).symm)

instance : (j)_!open⟦T⟧.IsLeftAdjoint :=
  (openImmersionLowerShriekUpperStarAdjunction T j).isLeftAdjoint

end OpenImmersion

/-! ### Lower shriek along a morphism admitting a compactification -/

section Compactification

variable {X Y : Scheme.{u}}

/-- The lower shriek on module objects associated with a compactification `X ⟶[i] Z ⟶[g] Y`
of `f`: the extension by zero `i_!` followed by the pushforward `g_*`. -/
noncomputable def compactificationLowerShriek {f : X ⟶ Y} (c : Compactification f) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (continuousMapRingObj T X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (continuousMapRingObj T Y) :=
  (c.i)_!open⟦T⟧ ⋙ (c.g)_*⟦T⟧

variable (f : X ⟶ Y) [HasCompactification f]

/-- The lower shriek `f_! : Mod_{A_X(T)} ⥤ Mod_{A_Y(T)}` along a morphism `f : X ⟶ Y` admitting
a compactification, on module objects over `C(-, T)`: the composition `i_! ⋙ g_*` associated
with the chosen compactification `HasCompactification.compactification f`. -/
noncomputable def lowerShriek :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (continuousMapRingObj T X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (continuousMapRingObj T Y) :=
  compactificationLowerShriek T (HasCompactification.compactification f)

@[inherit_doc lowerShriek]
scoped notation "(" f ")_!⟦" T "⟧" => lowerShriek T f

/-- The lower shriek `f_!` on module objects is the extension by zero along the open immersion
of the chosen compactification followed by the pushforward along its proper structure
morphism. -/
lemma lowerShriek_eq :
    (f)_!⟦T⟧ = ((HasCompactification.compactification f).i)_!open⟦T⟧ ⋙
      ((HasCompactification.compactification f).g)_*⟦T⟧ :=
  rfl

/-- The underlying sheaf of `f_! M` is `f_! M`. -/
lemma lowerShriek_comp_forget :
    (f)_!⟦T⟧ ⋙ Mod.forget (continuousMapRingObj T Y) =
      Mod.forget (continuousMapRingObj T X) ⋙ ProEtale.lowerShriek Ab.{u + 1} f := rfl

instance lowerShriek_additive : (f)_!⟦T⟧.Additive := by
  rw [lowerShriek_eq]
  infer_instance

/-- The lower shriek `f_!` on module objects is left exact, being the composition of the exact
extension by zero along the open immersion of the chosen compactification with the left exact
pushforward along its proper structure morphism. -/
instance preservesFiniteLimits_lowerShriek : PreservesFiniteLimits (f)_!⟦T⟧ := by
  rw [lowerShriek_eq]
  exact comp_preservesFiniteLimits _ _

end Compactification

end AlgebraicGeometry.ProEtale.ContinuousMapRing
