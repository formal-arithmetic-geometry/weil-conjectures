/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FormalFunctionsFinitePullback
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoB
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoR
@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry
/-- The canonical quotient-system isomorphism, with its factorization of pullback.
(Stacks, Tags 02OD, 089W, 01F7 and 01FB.) -/
theorem formalFunctions_finite_quotient_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
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
      ∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p),
        r n z = formalFunctionsFinitePullback f y F p n z := by
  dsimp
  obtain ⟨b, hb⟩ := formalFunctions_finite_quotient_iso_b f F hF y p
  obtain ⟨r, hr, hp⟩ := formalFunctions_finite_quotient_iso_r f F hF y p b hb
  exact ⟨b, r, hr, hp⟩
end AlgebraicGeometry
