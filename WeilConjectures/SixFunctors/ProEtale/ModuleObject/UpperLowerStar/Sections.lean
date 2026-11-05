/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-!
# Pullback of global sections of module objects

Let `Λ` be a commutative condensed ring. A global section of a module object `M` over
`Λ_T = p_T^* Λ` on a scheme `T` is a morphism `w : 𝟙_ ⟶ M` out of the unit `Λ_T`. Its pullback
along a morphism `a : S ⟶ T` is the global section `𝟙_ ≅ a^* 𝟙_ ⟶ a^* M` of `a^* M`. For
`M = b^* N` with `b : T ⟶ B` and `a ≫ b = t`, composing with `a^* b^* N ≅ (a ≫ b)^* N = t^* N`
gives a global section of `t^* N`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperStarSectionMap`). These pullbacks are
functorial: pulling back along `a'` and then along `a` is pulling back along `a ≫ a'`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperStarSectionMap_upperStarSectionMap`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {S T B : Scheme.{u}}

/-- The unit of module objects, written in the syntactic form of the type of the unit
comparisons `ε` of strong monoidal functors (see the implementation notes of
`WeilConjectures.WeilObject.Sheaf.StalkUnit`): as a notation rather than a definition, since the
kernel unfolds the pullbacks when a constant occurs as an argument of their components. -/
scoped notation "𝟙ₘ" =>
  @MonoidalCategoryStruct.tensorUnit _ _ MonoidalCategory.toMonoidalCategoryStruct

/-- The pullback of a global section `w : 𝟙_ ⟶ b^* N` along `a : S ⟶ T`, as a global section of
`t^* N` for `a ≫ b = t`: the composite `𝟙_ ≅ a^* 𝟙_ ⟶ a^* b^* N ≅ (a ≫ b)^* N = t^* N`. The
transport along `a ≫ b = t` is an `eqToHom` of objects, which keeps the kernel from unfolding
the pullbacks. -/
noncomputable def upperStarSectionMap (a : S ⟶ T) {b : T ⟶ B} {t : S ⟶ B} (h : a ≫ b = t)
    (N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B))
    (w : 𝟙ₘ ⟶ (b)^*⟦Λ⟧.obj N) : 𝟙ₘ ⟶ (t)^*⟦Λ⟧.obj N :=
  (Functor.Monoidal.εIso (a)^*⟦Λ⟧).hom ≫ (a)^*⟦Λ⟧.map w ≫
    (upperStarComp Λ a b).inv.app N ≫ eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj N) h)

end AlgebraicGeometry.ProEtale.CondensedRing
