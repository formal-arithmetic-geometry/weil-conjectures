/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom

/-! # The normalized open reduction mate from support -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The inverse open reduction mate is invertible once its target has open support.
Source: blueprint integral direct-image proof paragraph (2), exact slice tensor identity.
Proof: expand the inverse Hom correspondence as the open extension of the input
map followed by the open counit. The input map is the reduction of the integral
open unit followed by the pullback/reduction isomorphism. Fully faithful integral
extension by zero makes that unit invertible. Functors preserve its invertibility,
and the support hypothesis makes the remaining counit invertible. Their composite
is precisely the specified mate, with no choice of an additional comparison.
(blueprint: lem-sp-integral-tower-open-mate). -/
theorem open_reduction_isIso_of_support (s : Presentation l E)
    (q : ReductionGeometry l E s) {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (N : Integral l E U)
    (hsupport : IsIso ((s.operations.openOp j).derivedAdjunction.counit.app
      ((derivedReduction l E s T).obj
        ((CondensedRing.openImmersionLowerShriek
          (spIntegralCondensed l E) j).mapDerivedCategory.obj N)))) :
    IsIso (openReductionInverse l E s q j N) := by
  have hu : IsIso
      ((((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (spIntegralCondensed l E) j).ofNatIsoRight
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (spIntegralCondensed l E) j).symm).unit.app N)) := by
    change IsIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction'
        (spIntegralCondensed l E) j).unit.app N)
    infer_instance
  have := hsupport
  unfold openReductionInverse
  rw [Adjunction.homEquiv_counit]
  infer_instance

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
