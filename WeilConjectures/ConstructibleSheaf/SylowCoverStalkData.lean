/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.PGroup
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

import WeilConjectures.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor
import WeilConjectures.ConstructibleSheaf.ConnectedTorsorSubgroupQuotient
import WeilConjectures.ConstructibleSheaf.ConnectedTorsorModuleDescent
import Mathlib.GroupTheory.Sylow

/-!
# Sylow covers of finite locally constant sheaves

A finite locally constant sheaf `G` of `ZMod ℓ`-modules on a connected scheme `U` becomes, after
pullback along a connected finite étale cover `V ⟶ U` of degree prime to `ℓ`, the sheaf
associated with a finite-dimensional representation of a finite `ℓ`-group.

## Main results

- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_sylow_cover_stalk_data`

## Implementation details

The finite monodromy correspondence gives a connected finite `Q`-torsor on which `G` is
constant. For an `ℓ`-Sylow subgroup `H` of `Q`, the subgroup quotient gives the cover `V ⟶ U`,
of degree `[Q : H]`, and a connected `H`-torsor over `V` with the same total space. Module
descent along this `H`-torsor produces the representation and the associated-sheaf functor.

## References

- Stacks Project, Tags 0A3R, 0DV5 and 0DV6.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- **Sylow cover of a finite locally constant sheaf.** For a finite locally constant sheaf `G`
of `ZMod ℓ`-modules on a connected scheme `U`, there is a connected finite étale `v : V ⟶ U`
whose geometric fibres all have cardinality `d` prime to `ℓ`, a finite `ℓ`-group `P`, a
finite-dimensional representation `M` of `P` and an additive functor `T` from representations
of `P` to sheaves on `V_ét`, compatible with stalks, such that `T M ≅ v^* G` and `T` sends the
trivial representation to the constant sheaf. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_sylow_cover_stalk_data
    {U : Scheme.{u}} [ConnectedSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] :
    ∃ (V : Scheme.{u}) (v : V ⟶ U) (_ : IsFinite v) (_ : Etale v) (_ : ConnectedSpace V)
      (d : ℕ), ¬ ℓ ∣ d ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
        Nat.card (v.GeometricFiber s) = d) ∧
      ∃ (P : Type u) (_ : Group P) (_ : Finite P), IsPGroup ℓ P ∧
        ∃ (M : Rep.{u + 1} (ZMod ℓ) P) (_ : FiniteDimensional (ZMod ℓ) M.V)
          (T : Rep.{u + 1} (ZMod ℓ) P ⥤
            Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
          (_ : T.Additive),
          (∀ x : V, Nonempty
            (T ⋙ (V.uliftPointSmallEtale x).sheafFiber
                  (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) ⋙
                ModuleCat.restrictScalars.{u + 1}
                  (ULift.ringEquiv.symm.toRingHom : ZMod ℓ →+* ULift.{u + 1} (ZMod ℓ)) ≅
              forget₂ (Rep.{u + 1} (ZMod ℓ) P) (ModuleCat.{u + 1} (ZMod ℓ)))) ∧
          Nonempty (T.obj M ≅ (v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ∧
          Nonempty (T.obj (Rep.trivial (ZMod ℓ) P (ULift.{u + 1} (ZMod ℓ))) ≅
            (constantSheaf V.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
              (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))) := by
  classical
  obtain ⟨Q, hQ, hQfin, c, hc, A, hA, ⟨α⟩⟩ :=
    exists_finite_monodromy_trivializing_torsor ℓ G
  let H : Sylow ℓ Q := Classical.choice inferInstance
  obtain ⟨V, v, hvfin, hvet, hV, hcard, cH, hcH, e, he⟩ :=
    c.exists_connected_subgroup_quotient Q H.toSubgroup
  let C := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))
  have htriv : Nonempty ((cH.π)^*[C].obj ((v)^*[C].obj G) ≅
      (constantSheaf cH.P.smallEtaleTopology C).obj A) := by
    refine ⟨((upperStarComp C cH.π v).app G).symm ≪≫
      (upperStarComp C e.hom c.π (cH.π ≫ v) he.symm).app G ≪≫
      ((e.hom)^*[C]).mapIso α ≪≫
      (Scheme.upperStarConstantSheafIso C e.hom).app A⟩
  obtain ⟨M, hM, T, hT, hstalk, hG, hunit⟩ :=
    cH.exists_module_descent_stalk_functor ℓ H.toSubgroup ((v)^*[C].obj G) A htriv
  exact ⟨V, v, hvfin, hvet, hV, H.index, H.not_dvd_index, hcard,
    H.toSubgroup, inferInstance, inferInstance, H.isPGroup',
    M, hM, T, hT, hstalk, hG, hunit⟩

end AlgebraicGeometry
