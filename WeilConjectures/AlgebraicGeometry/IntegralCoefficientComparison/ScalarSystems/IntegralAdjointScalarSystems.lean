/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientComparison.IntegralAdjointFiniteFreeTowerData

/-! # Whole-system scalar coordinates
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (1)--(2).
All ordinary comparisons are normalized before localization, and all derived
comparisons retain their universal computation-counit equation.
(blueprint: def-pur-integral-adjoint-coefficient-data).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralCoefficientComparison
open IntegralDirectImageTower CurrentNativeIntegralTower
open WeilConjectures

variable (ell : ℕ) [Fact ell.Prime] (E F : Type u) [Field E] [Field F]
  [Algebra (Padic ell) E] [Algebra (Padic ell) F]
  [FiniteDimensional (Padic ell) E] [FiniteDimensional (Padic ell) F]
  (i : E →ₐ[Padic ell] F) (sE : Presentation ell E) (sF : Presentation ell F)

variable {ell E F i sE sF} in
variable {ell E F i sE sF} in
/-- Proper counit mate followed by the open scalar isomorphism, on whole systems.
Source: (2), b before inverse limit
(blueprint: def-pur-integral-adjoint-coefficient-data). -/
def ScalarSystems.compactMap (a : ScalarSystems ell E F i sE sF)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    SpTowerShriek.F ell E sE.base sE.operations c ⋙ (a.component Y).system.T ⟶
      (a.component X).system.T ⋙ SpTowerShriek.F ell F sF.base sF.operations c :=
  Functor.whiskerLeft (SpTowerShriek.openD ell E sE.base (sE.operations.openOp c.i))
    (mateEquiv (SpTowerShriek.adjunction ell E sE.base (sE.operations.geometry c.g))
      (SpTowerShriek.adjunction ell F sF.base (sF.operations.geometry c.g))
      (a.pull c.g).derived.hom).natTrans ≫
    Functor.whiskerRight (a.openIso c.i).hom
      (SpTowerShriek.push ell F sF.base (sF.operations.geometry c.g))

end AlgebraicGeometry.ProEtale.IntegralCoefficientComparison
