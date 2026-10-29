/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparisonIso
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.TateTwist.LocallyFree

/-!
# Pullbacks of the Tate twists

Let `f : X ⟶ Y` be a morphism of schemes and `ℓ` a prime. This file compares the pullback
`f^* ℚ̄_ℓ,Y(d)` of the Tate twists of `WeilConjectures.TateTwist.ProEtale` with `ℚ̄_ℓ,X(d)`, as
module objects over `ℚ̄_ℓ,X` and, placed in degree `0`, in the derived category.

* From an isomorphism `f^* ℚ̄_ℓ,Y(1) ≅ ℚ̄_ℓ,X(1)`, the strong monoidal structure of `f^*` gives
  `f^* ℚ̄_ℓ,Y(d) ≅ ℚ̄_ℓ,X(d)` for `d ≥ 0`
  (`AlgebraicGeometry.ProEtale.upperStarTateTwistNatIsoOfOne`) and, the Tate twists `ℚ̄_ℓ,Y(n)`
  being dualizable when `Y` lives over a field in which `ℓ` is invertible
  (`AlgebraicGeometry.ProEtale.isDualizable_tateTwistNat`), for all `d ∈ ℤ`
  (`AlgebraicGeometry.ProEtale.upperStarTateTwistIsoOfOne`): `f^*` commutes with the duals of
  dualizable objects. The derived version is
  `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTateTwistDerivedIsoOfOne`, since
  `Lf^*` of a sheaf placed in degree `0` is its pullback.
* For `d = 0` there is nothing to compare
  (`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTateTwistDerivedZeroIso`).
* The pullback of a free module is free: `f^*(Λ_Y ⊗ M) ≅ Λ_X ⊗ f^* M`
  (`AlgebraicGeometry.ProEtale.CondensedRing.freeUpperStarIso`), by uniqueness of left adjoints.
  This is the first step towards `f^* ℤ_ℓ,Y(1) ≅ ℤ_ℓ,X(1)`, `ℤ_ℓ(1) = lim_n ℤ_ℓ ⊗ μ_{ℓⁿ}`.

The isomorphism `f^* ℚ̄_ℓ,Y(1) ≅ ℚ̄_ℓ,X(1)` itself is not constructed here. It needs the
identification `f^* μ_{ℓⁿ,Y} ≅ μ_{ℓⁿ,X}` for a general `f` (only weakly étale `f` is treated, by
`ProEtale.upperStarRootsOfUnitySheafIso`), the commutation of `f^*` with the limit defining
`ℤ_ℓ(1)` (`ProEtale.preservesLimitsOfSize_upperStar_ab` for quasi-compact quasi-separated
schemes), and the commutation of `f^*` with extension of scalars (`CondensedRing.pullIso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits MonoidalClosed

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Mod

/-- The free module functor `M ↦ R ⊗ M` is left adjoint to the forgetful functor. -/
def freeFunctorForgetAdjunction {C : Type*} [Category* C] [MonoidalCategory C] (R : C)
    [MonObj R] : freeFunctor R ⊣ forget R :=
  freeForgetAdjunction R

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

/-! ### The pullback of free modules -/

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pullback of a free module is free: `f^*(Λ_Y ⊗ M) ≅ Λ_X ⊗ f^* M`, naturally in the sheaf
`M`. Both functors are left adjoint to `N ↦ f_* N`. -/
noncomputable def freeUpperStarIso :
    Mod.freeFunctor (condensedRingObj Λ Y) ⋙ (f)^*⟦Λ⟧ ≅
      (f)^*[Ab.{u + 1}] ⋙ Mod.freeFunctor (condensedRingObj Λ X) :=
  ((Mod.freeFunctorForgetAdjunction (condensedRingObj Λ Y)).comp
      (upperStarLowerStarAdjunction Λ f)).leftAdjointUniq
    ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).comp
      (Mod.freeFunctorForgetAdjunction (condensedRingObj Λ X)))

end CondensedRing

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The Tate twists from `ℚ̄_ℓ(1)` -/

/-- The pullback commutes with the duals of dualizable modules: the comparison map
`f^* [T, 𝟙] ⟶ [f^* T, f^* 𝟙]` of the strong monoidal pullback is an isomorphism for a dualizable
`T`. -/
lemma isIso_ihomComparison_upperStar_app_unit
    {T : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)} (hT : IsDualizable T) :
    IsIso ((Functor.LaxMonoidal.ihomComparison (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧ T).natTrans.app
      (𝟙_ _)) := by
  obtain ⟨_⟩ := hT
  let := BraidedCategory.exactPairing_swap T Tᘁ
  exact Functor.Monoidal.isIso_ihomComparison_app_unit_of_exactPairing _ Tᘁ T

variable (e : (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (tateTwistOne Y ℓ) ≅ tateTwistOne X ℓ)

/-- An isomorphism `f^* ℚ̄_ℓ,Y(1) ≅ ℚ̄_ℓ,X(1)` induces `f^* ℚ̄_ℓ,Y(d) ≅ ℚ̄_ℓ,X(d)` for `d ≥ 0`,
`f^*` being strong monoidal. -/
noncomputable def upperStarTateTwistNatIsoOfOne :
    (d : ℕ) → (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (tateTwistNat Y ℓ d) ≅ tateTwistNat X ℓ d
  | 0 => (Functor.Monoidal.εIso _).symm
  | d + 1 => (Functor.Monoidal.μIso _ _ _).symm ≪≫ (upperStarTateTwistNatIsoOfOne d ⊗ᵢ e)

/-- An isomorphism `f^* ℚ̄_ℓ,Y(1) ≅ ℚ̄_ℓ,X(1)` induces `f^* ℚ̄_ℓ,Y(d) ≅ ℚ̄_ℓ,X(d)` for all `d ∈ ℤ`,
provided the non-negative Tate twists of `Y` are dualizable: for `d < 0`, `ℚ̄_ℓ(d)` is the dual
`[ℚ̄_ℓ(-d), ℚ̄_ℓ]`, and the strong monoidal `f^*` commutes with duals of dualizable objects. -/
noncomputable def upperStarTateTwistIsoOfOne (hY : ∀ n : ℕ, IsDualizable (tateTwistNat Y ℓ n)) :
    (d : ℤ) → (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (tateTwist Y ℓ d) ≅ tateTwist X ℓ d
  | (d : ℕ) => upperStarTateTwistNatIsoOfOne f ℓ e d
  | .negSucc d =>
    have := isIso_ihomComparison_upperStar_app_unit f ℓ (hY (d + 1))
    Functor.LaxMonoidal.mapIhomObjIso _ (upperStarTateTwistNatIsoOfOne f ℓ e (d + 1))
      (Functor.Monoidal.εIso _).symm

/-- The non-negative Tate twists of a scheme over a field in which `ℓ` is invertible are
dualizable (`ProEtale.isLocallyFree_tateTwist`). -/
lemma isDualizable_tateTwistNat {k : Type u} [Field k] [NeZero (ℓ : k)]
    (p : Y ⟶ Spec (.of k)) (n : ℕ) : IsDualizable (tateTwistNat Y ℓ n) :=
  (isLocallyFree_tateTwist ℓ p n).isDualizable

namespace CondensedRing

/-- **The derived pullback of `ℚ̄_ℓ(0)`**: `Lf^* ℚ̄_ℓ,Y(0) ≅ ℚ̄_ℓ,X(0)`, both being the tensor units
placed in degree `0`. -/
noncomputable def leftDerivedUpperStarTateTwistDerivedZeroIso :
    L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (tateTwistDerived Y ℓ 0) ≅
      tateTwistDerived X ℓ 0 :=
  leftDerivedUpperStarSingleIso _ f _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (Functor.Monoidal.εIso _).symm

/-- **Derived pullback of the Tate twists**, given `f^* ℚ̄_ℓ,Y(1) ≅ ℚ̄_ℓ,X(1)`:
`Lf^* ℚ̄_ℓ,Y(d) ≅ ℚ̄_ℓ,X(d)` for all `d ∈ ℤ`, if the non-negative Tate twists of `Y` are
dualizable (e.g. `Y` over a field in which `ℓ` is invertible, `isDualizable_tateTwistNat`).
`Lf^*` of a sheaf placed in degree `0` is its pullback (`leftDerivedUpperStarSingleIso`). -/
noncomputable def leftDerivedUpperStarTateTwistDerivedIsoOfOne
    (hY : ∀ n : ℕ, IsDualizable (tateTwistNat Y ℓ n)) (d : ℤ) :
    L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (tateTwistDerived Y ℓ d) ≅
      tateTwistDerived X ℓ d :=
  leftDerivedUpperStarSingleIso _ f _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (upperStarTateTwistIsoOfOne f ℓ e hY d)

end CondensedRing

end AlgebraicGeometry.ProEtale
