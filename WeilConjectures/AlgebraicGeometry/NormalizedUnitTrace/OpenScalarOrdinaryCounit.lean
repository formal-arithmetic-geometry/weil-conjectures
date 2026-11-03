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

private local instance openScalarOrdinaryCounitBundledComm
    (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) :
    IsCommMonObj (CommMon.toMon (c.bundled.{u} ell)).X := by
  change IsCommMonObj (c.obj ell)
  infer_instance

/-- The ordinary scalar open mate preserves the coefficient-unit counit.
Source: smooth purity transport, Step 4, and open normalization, Step 5
(blueprint: lem-pur-open-scalar-ordinary-counit).

Proof: put J_R,J_Q for ordinary open extension and P_R,P_Q for exact derived
open pullback, S,T for scalar extension, e for the open scalar isomorphism,
and theta for the scalar/pullback mate. Iterated mates identify theta with the
open-adjunction mate of e.inv. Hence the mate counit equation says that J_Q of
theta followed by the Q-counit equals e.inv followed by T of the R-counit,
with the corresponding source pullback object.

The scalar/pullback unit square is proved by transposing through scalar
extension/restriction. Exact restriction and pullback commute with singles;
the transposed square on regular modules is naturality of coefficientMap with
condensedPullbackHom. The derived scalar unit is computed by the ordinary
adjunction on the flat regular module. This gives theta at the unit followed by
P_Q(u_Y) and the Q-pullback unit equals S of the R-pullback unit followed by u_X.

Precompose the mate counit equation with J_Q(u_X.inv). Use that unit square to
move the inverse pullback unit into the R-counit, and use counit naturality to
move u_Y to the output. Cancel the two specified pullback unit isomorphisms.
Transport from exact derived pullback to the left-derived presentation with
ofNatIsoRight; its counit formula inserts precisely the comparison displayed in
the statement. No smooth adjunction or purity normalization enters this equation. -/
theorem openScalarOrdinaryCounit
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    (actualOpen ((Coefficient.closure : Coefficient ell).obj ell) j.left).map
        (scalarUnitIso ell X.left).inv ≫
      (CondensedRing.derivedOpenImmersionShriekIso
        (Λ := (Coefficient.integers : Coefficient ell).obj ell)
        (Λ' := (Coefficient.closure : Coefficient ell).obj ell) (integralClosureMap ell).hom.hom
          j.left).inv.app
        (𝟙_ _) ≫
      (scalarSixChange (integralClosureMap ell) Y.left).map
        ((actualOpen ((Coefficient.integers : Coefficient ell).obj ell) j.left).map
            (CondensedRing.leftDerivedUpperStarUnitIso
              ((Coefficient.integers : Coefficient ell).obj ell) j.left).inv ≫
          ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
            ((Coefficient.integers : Coefficient ell).obj ell) j.left).ofNatIsoRight
              (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                ((Coefficient.integers : Coefficient ell).obj ell) j.left).symm).counit.app
                  (𝟙_ _)) ≫
      (scalarUnitIso ell Y.left).hom =
    (actualOpen ((Coefficient.closure : Coefficient ell).obj ell) j.left).map
        (CondensedRing.leftDerivedUpperStarUnitIso
          ((Coefficient.closure : Coefficient ell).obj ell) j.left).inv ≫
      ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
        ((Coefficient.closure : Coefficient ell).obj ell) j.left).ofNatIsoRight
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            ((Coefficient.closure : Coefficient ell).obj ell) j.left).symm).counit.app
              (𝟙_ _) := by
  sorry

end AlgebraicGeometry.ProEtale.NormalizedUnitTrace
