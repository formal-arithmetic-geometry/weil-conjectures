/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FormalFunctionsLocalStalkComparison
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteQuotientIso
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteQuotientMaps

/-! # Finite quotient cohomology on the local base change

## References

* Stacks Project, Tags 02OD, 089W and 01FB
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry
/-- The finite quotient system on the local base change is identified with the
infinitesimal fibre cohomology system. The theorem records only the finite-level
part of the geometric dictionary and leaves the stalk comparison separate.
(Stacks, Tags 02OD, 089W and 01FB.) -/
theorem formalFunctions_finite_quotient_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p : ℕ) :
    let X' := pullback (Y.fromSpecStalk y) f
    let f' := pullback.fst (Y.fromSpecStalk y) f
    let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
    let J := (Scheme.IdealSheafData.ofIdealTop
      ((maximalIdeal (Y.presheaf.stalk y)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap f'
    let C := RingedSpace.moduleCohomology X'.toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫ f'.appTop).hom
    ∃ b : formalCompletionSystem J F' ⋙ C ≅
      formalFibreCohomologySystem f y F p ⋙ ModuleCat.restrictScalars
        (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))),
    ∃ r : ∀ n : ℕ, formalFunctionsLocalCohomology f y F p →ₗ[Y.presheaf.stalk y]
      formalFibreCohomologyLocal f y F p n,
      (∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p),
        r n z = (b.hom.app (op n)) ((C.map (formalModuleQuotientπ J (n + 1) F')) z)) ∧
      ∀ a : formalFunctionsStalk f y F p →ₗ[Y.presheaf.stalk y]
          formalFunctionsLocalCohomology f y F p,
        IsFormalFunctionsLocalComparison f y F p a →
          ∀ n : ℕ, IsFormalFunctionsTheta f y F p n ((r n).comp a) := by
  dsimp
  obtain ⟨b, r, hr, hpull⟩ := formalFunctions_finite_quotient_iso f F hF y p
  refine ⟨b, r, hr, ?_⟩
  intro a ha n
  exact formalFunctions_finite_quotient_maps f F hF y p n (r n) (hpull n) a ha
end AlgebraicGeometry
