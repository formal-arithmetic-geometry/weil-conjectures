/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.ProjectiveBundleFormula
public import WeilConjectures.AlgebraicGeometry.KummerAdditivity
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
import WeilConjectures.AlgebraicGeometry.Picard.UniversalAdjointSection

/-! # Naturality of the specified Kummer Chern arrow

The projective-bundle construction uses `kummerFirstChern`. Identify that arrow
with the canonical arbitrary-base Chern realization before applying pullback.
Source: Stacks Tags 03PL and 03FD; equation-chern-classes in Tag 0FI5.
(blueprint: lem-pur-chern-kummer-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

private theorem kummerFirstChern_eq_canonical (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (M : T.Pic) :
    kummerFirstChern A N hA T hT M = ordinaryFiniteFirstChern A N hA T hT M := by
  apply ordinaryFiniteFirstChern_unique A N hA T hT M
  unfold kummerFirstChern kummerFirstChernAbelian
  exact (Equiv.ofBijective
    (ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2)
    (kummerFirstChernRealization_bijective A T _)).apply_symm_apply _

/-- The Kummer arrow used to define projective hyperplane classes is natural on
arbitrary bases; no finiteness condition on the pulled-back scheme is needed.
Source: Stacks Tags 03PL and 03FD, naturality of the Kummer connecting class.
Proof: the class bijection identifies this specified arrow with
ordinaryFiniteFirstChern. Apply the arbitrary-base pullback theorem for that
canonical arrow and identify it again with the specified Kummer arrow.
(blueprint: lem-pur-chern-kummer-naturality). -/
theorem kummerFirstChern_pullback_arbitraryBase (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))) (M : Y.Pic) :
    ordinaryFiniteLinePullbackMap A N hA t f hY (kummerFirstChern A N hA Y hY M) =
      kummerFirstChern A N hA X hX (Scheme.Pic.map f M) := by
  rw [kummerFirstChern_eq_canonical, kummerFirstChern_eq_canonical]
  exact ordinaryFiniteFirstChern_pullback A N hA t f hY hX M

end AlgebraicGeometry.Etale

namespace WeilConjectures.PurityFiniteSetting

/-- The normalized tautological comparison identifies the pulled-back hyperplane
Chern class. This uses only its actual line isomorphism, not any purity theorem.
Source: Stacks Tag 01O3, degree-one twist comparison, and Tag 03PL, Kummer naturality.
Proof: the tensor-pullback/adjoint-pullback comparison followed by theta identifies
the Picard classes. Apply arbitrary-base naturality of the specified Kummer arrow.
(blueprint: lem-pur-chern-kummer-naturality). -/
theorem projectiveBundleChern_pullback (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T T' : Scheme.{u}}
    {F : T.Modules} {F' : T'.Modules}
    (a : T ⟶ Spec (.of P.field.k)) (a' : T' ⟶ Spec (.of P.field.k))
    (g : T' ⟶ T) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (D : ProjectiveBundleRealization T F) (D' : ProjectiveBundleRealization T' F')
    (hL : D.L.IsInvertible) (hL' : D'.L.IsInvertible)
    (b : ProjectiveBundleBaseChangeDatum D D' g e) :
    Etale.ordinaryFiniteLinePullbackMap P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t b.map
        (P.diagonalExponent_isUnit (D.A.data.relProjHom ≫ a))
        (P.projectiveBundleChern a D hL) = P.projectiveBundleChern a' D' hL' := by
  have := hL
  have := hL'
  have hPic : Scheme.Pic.map b.map (Scheme.Pic.ofIsInvertible D.L) =
      Scheme.Pic.ofIsInvertible D'.L := by
    rw [Scheme.Pic.map_ofIsInvertible]
    exact Scheme.Pic.ofIsInvertible_eq_of_iso
      (((projectiveBundleTensorPullbackIso b.map).app D.L).symm ≪≫ b.theta)
  unfold projectiveBundleChern
  rw [Etale.kummerFirstChern_pullback_arbitraryBase
    P.Coefficient P.diagonalExponent P.diagonalExponent_annihilates t b.map
    (P.diagonalExponent_isUnit (D.A.data.relProjHom ≫ a))
    (P.diagonalExponent_isUnit (D'.A.data.relProjHom ≫ a'))]
  rw [hPic]

end WeilConjectures.PurityFiniteSetting
