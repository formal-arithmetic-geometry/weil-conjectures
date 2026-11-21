/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Presentable.Finite
public import WeilConjectures.AlgebraicGeometry.Sites.FilteredColimitSections
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# Extensions by zero of constant sheaves are finitely presentable

Let `v : V ⟶ X` be étale with `V` quasi-compact and quasi-separated. The extension by zero
`v_! Λ` of the constant sheaf `Λ` on `V_ét` is a finitely presentable étale sheaf of
`Λ`-modules on `X`: `Hom(v_! Λ, G) = Γ(V, v^* G)`, and sections over the quasi-compact
quasi-separated `V` commute with filtered colimits.

## Main statements

- `ModuleCat.isFinitelyPresentable_self`: the free module of rank one is finitely presentable.
- `AlgebraicGeometry.Etale.isFinitelyPresentable_constantSheaf`: the constant sheaf `Λ` on a
  quasi-compact quasi-separated scheme is finitely presentable.
- `AlgebraicGeometry.Etale.isFinitelyPresentable_etaleLowerShriek_constantSheaf`: so is its
  extension by zero along an étale morphism.

## References

* [Stacks, Tag 0738]
* [Stacks, Tag 095N]
* [Stacks, Tag 09Z4]
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable {Λ : Type (u + 1)} [CommRing Λ]

namespace ModuleCat

/-- Linear maps out of the free module of rank one are elements of the target. -/
noncomputable def coyonedaObjSelfIsoForget :
    coyoneda.obj (op (ModuleCat.of Λ Λ)) ≅ CategoryTheory.forget (ModuleCat.{u + 1} Λ) :=
  NatIso.ofComponents fun N ↦ Equiv.toIso
    { toFun f := f.hom 1
      invFun n := ModuleCat.ofHom (LinearMap.toSpanSingleton Λ N n)
      left_inv f := ModuleCat.hom_ext (LinearMap.ext_ring (by simp))
      right_inv n := by simp }

/-- The free module of rank one is finitely presentable, for colimits of `u`-small filtered
diagrams. -/
theorem isFinitelyPresentable_self : IsFinitelyPresentable.{u} (ModuleCat.of Λ Λ) := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact ⟨fun _ _ _ ↦ preservesColimitsOfShape_of_natIso coyonedaObjSelfIsoForget.symm⟩

end ModuleCat

namespace AlgebraicGeometry

open Scheme Etale

/-- **The constant sheaf on a quasi-compact quasi-separated scheme is finitely presentable.** -/
theorem Etale.isFinitelyPresentable_constantSheaf (V : Scheme.{u}) [CompactSpace V]
    [QuasiSeparatedSpace V] :
    IsFinitelyPresentable.{u} ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ)) := by
  let T : V.Etale := Scheme.Etale.mk (𝟙 V)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
  have : CompactSpace T.left := ‹CompactSpace V›
  have : QuasiSeparatedSpace T.left := ‹QuasiSeparatedSpace V›
  have : Functor.IsCardinalAccessible.{u}
      ((sheafSections V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op T))
      Cardinal.aleph0 :=
    Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize.2 inferInstance
  have := ModuleCat.isFinitelyPresentable_self (Λ := Λ)
  exact (constantSheafAdj _ _ hT).isCardinalPresentable_leftAdjoint_obj _ _

/-- **Extensions by zero of constant sheaves are finitely presentable.** For an étale
`v : V ⟶ X` with `V` quasi-compact and quasi-separated, `v_! Λ` is a finitely presentable étale
sheaf of `Λ`-modules. -/
theorem Etale.isFinitelyPresentable_etaleLowerShriek_constantSheaf {V X : Scheme.{u}}
    (v : V ⟶ X) (h : Etale v) [CompactSpace V] [QuasiSeparatedSpace V] :
    IsFinitelyPresentable.{u} ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v h).obj
      ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))) := by
  have := Etale.isFinitelyPresentable_constantSheaf (Λ := Λ) V
  have : PreservesColimitsOfSize.{u, u} ((v)^*[ModuleCat.{u + 1} Λ]) :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).leftAdjoint_preservesColimits
  exact (Etale.etaleLowerShriekUpperStarAdjunction _ v h).isCardinalPresentable_leftAdjoint_obj
    _ _

end AlgebraicGeometry
