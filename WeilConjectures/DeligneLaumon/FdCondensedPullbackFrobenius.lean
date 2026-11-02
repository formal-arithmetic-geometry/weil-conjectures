/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedFibresExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Roots
import WeilConjectures.DeligneLaumon.CondensedPullbackPowerTransport
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackConstantModelConstructible
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Finiteness.Basic

/-! # Residue-degree Frobenius for condensed coefficient pullback

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.proof.md, Steps 1 and 2
(blueprint: lem-fd-condensed-pullback-frobenius).

All fibres are sections of actual condensed module inverse images. The coefficients are
finite-subextension-valued continuous functions. The scalar field is the standard lift
`ULift (PadicAlgCl l)` used by the existing fibre functor, with its canonical ring equivalence
with `PadicAlgCl l`. The comparison below is the specified pullback compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The canonical geometric-fibre comparison: inverse of the composition isomorphism,
then transport through compatibility of the two chosen geometric points, then sections.
Source: latest blueprint, Step 2, pullback along the first projection
(blueprint: lem-fd-condensed-pullback-frobenius). -/
def fdCondensedFibreComparison (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (z : Spec (.of D.k) ⟶ X) (x : Spec (.of D.k) ⟶ Y) (h : z ≫ f = x)
    (M : CondensedModule.Modules l Y) :
    CondensedModule.fibre l D
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M) z ≅
      CondensedModule.fibre l D M x :=
  (CondensedRing.pointSections l D.k).mapIso
    ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) z f).symm.app M ≪≫
      (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) h).app M)

attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp
  CondensedRing.upperStarFromPointMod CondensedRing.upperStarIsoIdOfIsSepClosed
  CondensedRing.pointSections

end WeilConjectures
