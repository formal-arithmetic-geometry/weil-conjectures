/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
import WeilConjectures.TateTwist.ProEtale
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueQuotient
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.AlgebraicGeometry.Affine.AffineRootsRepresentability
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTateTowerLimit

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-canonical-pullback). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- Scalar association applied to an integral-root comparison, in a generic
coefficient ring. Source: Cartesianity of scalar extension
(blueprint: def-pur-transport-canonical-pullback). -/
def scalarPull
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)}
    {N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)}
    (e : (CondensedRing.upperStar R f).obj M ≅ N) :=
  (CondensedRing.pullIso a f).symm.app M ≪≫
    (Mod.extendScalars (coefficientMap a X)).mapIso e

end AlgebraicGeometry.ProEtale.PurityTransport
