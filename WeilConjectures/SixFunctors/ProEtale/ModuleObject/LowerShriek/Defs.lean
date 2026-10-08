/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!

# Lower shriek on module objects over `C(-, T)`

Let `T` be a commutative topological ring. The canonical coefficient morphism
`α_j : j^* A_X(T) ⟶ A_U(T)` is an isomorphism for every open immersion `j : U ⟶ X`
(`ProEtale.isIso_continuousMapPullbackHom_of_isOpenImmersion`). This file defines the extension
by zero along open immersions and the lower shriek along morphisms admitting a compactification
on the categories `Mod_{A_X(T)}` of module objects, following the geometric route (open
immersions, then compactifications) rather than a global projection-formula lift.

* For an open immersion `j : U ⟶ X`, the pullback `j^* : Mod_{A_X(T)} ⥤ Mod_{A_U(T)}` on module
  objects is `mapMod(j^*)` followed by extension of scalars along the isomorphism `α_j`, so it is
  `mapMod(j^*)` up to equivalence; its underlying sheaf functor `j^*` has the exact left adjoint
  `j_!` on sheaves, which lifts to module objects through the projection formula
  `j_!(j^* L ⊗ M) ≅ L ⊗ j_! M`. Here the extension by zero on module objects is *defined* as a
  left adjoint of `j^*`, by the characterization `j_! ⊣ j^*`
  (`ProEtale.ContinuousMapRing.openImmersionLowerShriek`, notation `(j)_!open⟦T⟧`): the
  existence of the left adjoint
  (`ProEtale.ContinuousMapRing.isRightAdjoint_upperStar_of_isOpenImmersion`) and its exactness
  (`ProEtale.ContinuousMapRing.preservesFiniteLimits_openImmersionLowerShriek`) are the two
  geometric inputs, currently `sorry`ed, see below.
* For a compactification `X ⟶[i] Z ⟶[g] Y` of `f : X ⟶ Y`, the lower shriek is
  `f_! := i_! ⋙ g_*` (`ProEtale.ContinuousMapRing.compactificationLowerShriek`), and for `f`
  with a chosen compactification `HasCompactification.compactification f` it is
  `ProEtale.ContinuousMapRing.lowerShriek`, notation `(f)_!⟦T⟧`, *definitionally* the
  composition for the chosen compactification (`ProEtale.ContinuousMapRing.lowerShriek_eq`).

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs`.

## Sorried input

* `ProEtale.ContinuousMapRing.isRightAdjoint_upperStar_of_isOpenImmersion`: for an open
  immersion `j`, the pullback `j^*` on module objects has a left adjoint. The left adjoint sends
  an `A_U(T)`-module `M` to the sheaf `j_! M` with the `A_X(T)`-action
  `A_X(T) ⊗ j_! M ≅ j_!(j^* A_X(T) ⊗ M) ⟶ j_!(A_U(T) ⊗ M) ⟶ j_! M` given by the projection
  formula for `j_!`, the isomorphism `α_j` and the action of `A_U(T)` on `M`; the adjunction is
  the adjunction `j_! ⊣ j^*` on sheaves together with the identification of `j^*` on module
  objects with `mapMod(j^*)` along `α_j`.
* `ProEtale.ContinuousMapRing.preservesFiniteLimits_openImmersionLowerShriek`: the extension
  by zero on module objects is left exact. Indeed its underlying sheaf functor is the exact
  `j_!` on sheaves, and finite limits of module objects are computed on the underlying sheaves.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale.ContinuousMapRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-! ### Extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For an open immersion `j`, the pullback `j^*` on module objects over `C(-, T)` has a left
adjoint, the extension by zero. See the module docstring. -/
instance isRightAdjoint_upperStar_of_isOpenImmersion : (j)^*⟦T⟧.IsRightAdjoint := sorry

/-- The extension by zero `j_! : Mod_{A_U(T)} ⥤ Mod_{A_X(T)}` along an open immersion
`j : U ⟶ X` on module objects over `C(-, T)`: *by definition* a chosen left adjoint of the
pullback `j^*` on module objects. Its underlying sheaf is the extension by zero `j_! M` of the
underlying sheaf, with the `A_X(T)`-action induced by the projection formula and `α_j`. -/
noncomputable def openImmersionLowerShriek :
    Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (continuousMapRingObj T U) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (continuousMapRingObj T X) :=
  (j)^*⟦T⟧.leftAdjoint

@[inherit_doc openImmersionLowerShriek]
scoped notation "(" j ")_!open⟦" T "⟧" => openImmersionLowerShriek T j

/-- The adjunction `j_! ⊣ j^*` on module objects along an open immersion. -/
noncomputable def openImmersionLowerShriekUpperStarAdjunction : (j)_!open⟦T⟧ ⊣ (j)^*⟦T⟧ :=
  Adjunction.ofIsRightAdjoint _

instance : (j)_!open⟦T⟧.IsLeftAdjoint :=
  (openImmersionLowerShriekUpperStarAdjunction T j).isLeftAdjoint

/-- The extension by zero on module objects is additive, being a left adjoint. -/
instance openImmersionLowerShriek_additive : (j)_!open⟦T⟧.Additive :=
  (openImmersionLowerShriekUpperStarAdjunction T j).left_adjoint_additive

/-- The extension by zero on module objects preserves all colimits of size `0`, being a left
adjoint. -/
noncomputable instance preservesColimitsOfSize_openImmersionLowerShriek :
    PreservesColimitsOfSize.{0, 0} (j)_!open⟦T⟧ :=
  (openImmersionLowerShriekUpperStarAdjunction T j).leftAdjoint_preservesColimits

/-- The extension by zero on module objects along an open immersion is left exact: its
underlying sheaf functor is the exact extension by zero on sheaves. See the module
docstring. -/
instance preservesFiniteLimits_openImmersionLowerShriek :
    PreservesFiniteLimits (j)_!open⟦T⟧ := sorry

/-- The extension by zero on module objects along an open immersion is exact. -/
instance preservesHomology_openImmersionLowerShriek : (j)_!open⟦T⟧.PreservesHomology :=
  -- the two fields of `PreservesHomology` are `autoParam`s, found by instance synthesis
  -- from `preservesFiniteLimits_openImmersionLowerShriek` and from the preservation of
  -- colimits of a left adjoint
  {}

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
