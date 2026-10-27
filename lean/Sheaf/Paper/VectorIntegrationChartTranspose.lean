/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.Paper.VectorIntegrationUnitTranspose

/-! # Restricting the actual integration adjunct to an inverse linear chart

Source: blueprint latest, sec-smooth-purity/sk-prop-an,
thm-amb-vector-bundle-purity.proof.md, second paragraph.
(blueprint: lem-pur-vector-chart-restricted-affine-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationChart
open AffineLinePurity AffineSpacePurity VectorIntegrationSite

/-- Restricting the global ordinary integration adjunct gives the ordinary ordered
counit adjunct on the affine chart. This assertion uses no ordered purity map.
Source: thm-amb-vector-bundle-purity.proof.md, second paragraph
(blueprint: lem-pur-vector-chart-restricted-affine-transpose).

Proof: let a be the inverse frame, f the bundle projection, p the affine projection,
and b the open inclusion. Their square is Cartesian. The normalization in
existsUnique_vectorIntegrationGluing identifies b* integration, followed by the
unit pullback, with compact-support exchange, the canonical chart coefficient map,
and the ordered affine counit. Invert compact-support exchange. Naturality of the
ordinary Hom bijection across its mate gives
  a*(adj_f integration) ; exceptionalExchange ; p!(unitPullback)
  = adj_p (inverseExchange ; b*integration ; unitPullback).
Here p! in this displayed formula denotes the exceptional right adjoint. Substitute
the normalized trace on the right. Source naturality of adj_p moves the inverse
Tate pullback and pullback compositor inside that adjunction. The canonical
coefficient identity is obtained by composing the pullback tensor comparison around
the Cartesian square: the chart coefficient, preceded by the inverse pullback for
a;f and its compositor, is the inverse of affineLinearCoefficientDescent followed
by inverse base-coefficient pullback for p. Prove that identity by induction on d;
at zero it is constant-unit pullback coherence, and at a successor use the tensor
pullback compositor, shifted Tate-line pullback coherence and the induction
hypothesis. Thus the arrow inside the adjunct is precisely the ordered trace used
in affineTransposeRaw. Apply exact comparison and then the HEq specification of
affineTranspose. At rank zero the same computation uses identity adjunctions;
empty opens require no separate existence or nonemptiness assumption. -/
theorem chartTranspose_eq_affine (P : WeilConjectures.PurityFiniteSetting.{u})
    (Z : Scheme.{u}) [IsNoetherian Z] (aZ : Z ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    (d : ℕ) (F : Z.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U : Z.Opens) (e : VectorBundleZeroSection.Trivialization Z d F U)
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) :
    letI : IsNoetherian U.toScheme := isNoetherian_of_locallyOfFiniteType (U.ι ≫ aZ)
    HEq (restrictedRaw P Z aZ d F U e r hA)
      (affineTranspose P U.toScheme (U.ι ≫ aZ) d r hA) := by
  sorry

end AlgebraicGeometry.ProEtale.VectorIntegrationChart
