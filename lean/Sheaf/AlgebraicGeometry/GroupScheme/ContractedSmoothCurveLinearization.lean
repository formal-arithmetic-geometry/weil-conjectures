module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.GroupScheme.RelativeAdditiveCoordinates
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Étale local linearization of a contracted smooth group curve

Source: Conrad, Reductive group schemes, Lemma 4.2.2, printed pp.117–119.
(blueprint: lem-sfb-contracted-smooth-curve-linearization).

All action identities test arbitrary algebras, including nonreduced algebras.
The tangent condition uses the character t^n, not its integer differential.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

open RelativeAdditiveCoordinates

/-- A smooth affine contracted group curve with additive geometric fibres and a
pure positive tangent character is étale locally equivariantly the additive group.

Source: Conrad, Lemma 4.2.2 and preceding étale localization, pp.117–119.
(blueprint: lem-sfb-contracted-smooth-curve-linearization).

Proof plan:
1. Smoothness gives finite projective differentials (lem-weil-pbc-smooth-ring-map-iff-smooth-affine,
   def-weil-pbc-smooth-ring-map). Pull them back along the identity. The universal derivation
   identifies tangent points with the dual of this cotangent module
   (def-weil-pbc-kahler-differentials); multiplication adds first-order coefficients.
2. Tensor–Hom for finite projective modules and differentials base change
   (lem-weil-pbc-kahler-differentials-base-change) identify tangent points after any base change.
   This respects the full action coaction, hence the geometric fibre character is t^n.
3. On an additive geometric fibre the action polynomial has a polynomial inverse. Degrees
   force it to be c(t)x. Laurent units and the identity at t=1 give t^m x; the tangent
   character comparison gives m=n, as an equality of scheme actions.
4. The identity is closed since U is affine and separated
   (lem-weil-pbc-affine-source-morphism-separated,
   lem-weil-pbc-section-separated-closed-immersion). Its complement is smooth and surjective
   (lem-pc-open-immersion-smooth-composition). Apply lem-sfb-smooth-space-cover-etale-sections
   and refine by affine opens, giving nonidentity sections. Smoothness persists under base
   change (lem-pc-proper-base-change). Use the empty cover when the base is empty.
5. Extend the orbit of such a section to q:A^1_R → U_R by contraction. Localization
   R[z] → R[z,z^-1] is injective, giving equivariance and uniqueness. Geometric fibres,
   normalized to send the chosen section to 1, have q(z)=z^n.
6. The fixed subgroup for mu_n is smooth and finitely presented
   (lem-sfb-mu-n-fixed-subgroup-smooth) and equals U on geometric fibres. Its inclusion is
   locally finitely presented (lem-sfb-space-relative-lfp-permanence), and its source is flat
   (lem-pc-smooth-flat). The isomorphism clause of
   lem-sfb-flat-geometric-fibre-open-criterion makes the inclusion an isomorphism.
7. Invariance under the full mu_n makes every coordinate polynomial lie in R[z^n]: compare
   coefficients in the basis 1,v,...,v^(n-1) of R[v]/(v^n-1). Factor q uniquely through
   z ↦ z^n to obtain qbar:A^1_R → U_R with qbar(t^n x)=t.qbar(x).
8. Every geometric fibre of qbar is the identity in the normalized coordinate. Its source
   is smooth (sbc-lem-affine-space-smooth), hence flat (lem-pc-smooth-flat); it is locally
   finitely presented by lem-sfb-space-relative-lfp-permanence. Apply
   lem-sfb-flat-geometric-fibre-open-criterion to make qbar a scheme isomorphism.
9. Transfer multiplication to m(x,y) in R[x,y]. Equivariance compares t-exponents
   n(i+j) and n, so positivity kills every term except degree one. Unit identities give
   m=x+y. Thus qbar is a group isomorphism, with the displayed identity after every algebra
   extension. No inversion of n, reducedness, Noetherianity or initial section is used. -/
theorem contracted_smooth_curve_etale_linearization
    (A : Type u) [CommRing A] (U : Over (Spec (.of A))) [GrpObj U]
    [IsAffine U.left] [Smooth U.hom] [LocallyOfFinitePresentation U.hom]
    [ModObj (RingGroupSchemes.multiplicative A).X U]
    (haut : ∀ (B : Type u) [CommRing B] [Algebra A B]
      (t : points (RingGroupSchemes.multiplicative A).X B) (x y : points U B),
      t • (x * y) = (t • x) * (t • y))
    (hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
      ∃ q : line A Ω ⟶ U, IsAdditiveCoordinate A U Ω q)
    (hcontract : ∀ (B : Type u) [CommRing B] [Algebra A B] (x : points U B),
      ∃ q : line A B ⟶ U, point A B B 0 ≫ q = 1 ∧
        ∀ (D : Type u) [CommRing D] [Algebra A D] [Algebra B D] [IsScalarTower A B D]
          (t : points (RingGroupSchemes.multiplicative A).X D),
          point A B D (unitValue A D t) ≫ q =
            t • points.map U (IsScalarTower.toAlgHom A B D) x)
    (hrank : (GrpObj.lieAlgebraSheaf U).IsFiniteLocallyFreeOfRank 1)
    (n : ℕ) (hn : 0 < n)
    (hweight : ∀ (B : Type u) [CommRing B] [Algebra A B]
      (t : points (RingGroupSchemes.multiplicative A).X B)
      (v : points U (DualNumber B)),
      points.map U (TrivSqZeroExt.fstHom A B B) v = 1 →
        points.map (RingGroupSchemes.multiplicative A).X
            ((Algebra.ofId B (DualNumber B)).restrictScalars A) t • v =
          points.map U ((DualNumber.scale (unitValue A B t ^ n)).restrictScalars A) v) :
    ∃ (I : Type u) (R : I → Type u) (_ : ∀ i, CommRing (R i))
      (_ : ∀ i, Algebra A (R i)),
      (∀ i, Etale (Spec.map (CommRingCat.ofHom (algebraMap A (R i))))) ∧
      (∀ s : Spec (.of A), ∃ (i : I) (r : Spec (.of (R i))),
        (Spec.map (CommRingCat.ofHom (algebraMap A (R i)))) r = s) ∧
      ∀ i, ∃ q : line A (R i) ⟶ U, IsAdditiveCoordinate A U (R i) q ∧
        ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra (R i) B]
          [IsScalarTower A (R i) B]
          (t : points (RingGroupSchemes.multiplicative A).X B) (x : B),
          point A (R i) B (unitValue A B t ^ n * x) ≫ q =
            t • (point A (R i) B x ≫ q) := by
  sorry

end AlgebraicGeometry
