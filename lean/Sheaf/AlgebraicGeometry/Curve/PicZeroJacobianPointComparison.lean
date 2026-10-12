/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible
import Sheaf.AlgebraicGeometry.BaseChangeCurve
import Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Picard pullback as extension of Jacobian points

Source: blueprint sec-curve-estimates/sk-prop-ext-invariance,
`lem-sc-piczero-torsion-base-change`, steps 1 and 2.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

set_option autoImplicit false

/-- The degree-zero Picard comparison is extension of points of one abelian variety.

Source: blueprint sec-curve-estimates/sk-prop-ext-invariance,
`lem-sc-piczero-torsion-base-change`, steps 1 and 2.
(blueprint: lem-sc-piczero-jacobian-point-comparison)

Proof: smoothness implies regularity and geometric reducedness. Connectedness over the
algebraically closed field implies geometric connectedness; regularity then gives geometric
irreducibility. Dimension one makes the curve smooth of relative dimension one. Apply Jacobian
representability, including compatibility with tensor product, to identify G with J(k).
Apply representability after base change, which preserves connectedness, smoothness, properness
and dimension one. The base-change compatibility of the degree-zero Picard functor identifies
its representing object with J base changed to k'. By the pullback adjunction its k'-points
are morphisms Spec k' to J over k. The compatibility square for the sheafification units says
that the image of a Picard class is its specified pullback, hence gives the displayed equality.
The subgroup equalities identify the given models G and G' with the degree-zero subgroups;
the group-law compatibility makes both identifications multiplicative equivalences. No choice
of an arbitrary point is involved. Identity extensions and genus zero satisfy the same square.
-/
theorem pic_zero_jacobian_point_comparison
    {k k' : Type u} [Field k] [Field k'] [IsAlgClosed k] [IsAlgClosed k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f]
    (G : Subgroup X.Pic) (hG : (G : Set X.Pic) = f.picZero)
    (G' : Subgroup (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Pic)
    (hG' : (G' : Set (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Pic) =
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).picZero)
    (j : G →* G')
    (hj : ∀ L : G, (j L).val = Scheme.Pic.mapHom
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) L.val)
    : ∃ (J : Over (Spec (.of k))) (hJ : CommGrpObj J),
      letI := hJ
      ∃ (_ : IsAbelianVariety J) (e : G ≃* (𝟙_ (Over (Spec (.of k))) ⟶ J))
        (e' : G' ≃* (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ⟶ J)),
      ∀ x : G, e' (j x) =
        toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ≫ e x := by
  sorry

end AlgebraicGeometry
