/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ComparisonBrownExplicit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek

/-! # Open scalar coordinate calculations -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NormalizedUnitTrace
open Scheme CondensedRing PurityTransport ExplicitSmoothComparison

private local instance openScalarSupportComparisonBundledComm
    (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) :
    IsCommMonObj (CommMon.toMon (c.bundled.{u} ell)).X := by
  change IsCommMonObj (c.obj ell)
  infer_instance

/-- The specified compactification comparison commutes with the scalar open mate.
Source: smooth purity transport, Steps 2--4, and scalar-refinement pasting
(blueprint: lem-pur-open-scalar-support-comparison).

Proof: identify scalarDirectMate with the native scalarDirectImageMate using
scalarDirectMate_eq, whose proof is equality of their normalized pullback maps.
Thus scalarSupportMap evaluated at K is the native sfbScalarCompactComparison.
Choose a common dense boundary refinement d of the chosen and trivial
compactifications, with maps r1 and r2. Write rho_c for their refinement
components. Canonical comparison normalization says CC_R followed by rho_R(r2)
equals rho_R(r1), and the same equation holds over the closure.

Scalar-refinement pasting says T(rho_R(r)) followed by beta_d equals beta_c
followed by rho_Q(r) at S(K). Postcompose the proposed CC/scalar square with
rho_Q(r2). Substitute this pasting identity twice and the two CC normalization
equations. Both sides become beta_c1 followed by rho_Q(r1). Cancel rho_Q(r2),
which is invertible on the localizing closure. The coefficient unit belongs to
that closure; S(unit) does too, since scalarUnitIso identifies it with the closure
unit. Naturality of the closure CC moves scalarUnitIso through this square.

On the trivial compactification the proper factor is the identity. Specialize
scalar pullback composition coherence to two identities. Conjugating by the
pullback unit isomorphisms makes its comparison an idempotent automorphism;
cancellation makes it the identity. The mate counit equation now shows that the
proper scalar mate commutes with the identity direct-image comparison. Comparing
the exact and total-derived pullback presentations through their resolution
counits preserves this equation and identifies its conjugate with identityPush.
Thus the trivial support map, followed by identityPush, is the published
derivedOpenImmersionShriekIso. Substituting both openUnitComparison definitions
gives the displayed square. -/
theorem openScalarSupportComparison
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    (scalarSixChange (integralClosureMap ell) Y.left).map
        (openUnitComparison ell .integers (integersAdmissible ell) j).hom ≫
      (CondensedRing.derivedOpenImmersionShriekIso
        (Λ := (Coefficient.integers : Coefficient ell).obj ell)
        (Λ' := (Coefficient.closure : Coefficient ell).obj ell) (integralClosureMap ell).hom.hom
          j.left).hom.app
        (𝟙_ _) ≫
      (actualOpen ((Coefficient.closure : Coefficient ell).obj ell) j.left).map
        (scalarUnitIso ell X.left).hom =
    (scalarSupportMap (integralClosureMap ell) (compactificationOverField j)).app (𝟙_ _) ≫
      (CondensedRing.rightDerivedLowerShriekOfCompactification
        ((Coefficient.closure : Coefficient ell).obj ell) (compactificationOverField j)).map
        (scalarUnitIso ell X.left).hom ≫
      (openUnitComparison ell .closure (closureAdmissible ell) j).hom := by
  sorry

end AlgebraicGeometry.ProEtale.NormalizedUnitTrace
