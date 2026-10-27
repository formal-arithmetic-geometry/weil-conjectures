module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Additive coordinates on group schemes over arbitrary rings

Source: Conrad, Reductive group schemes, Lemma 4.2.2, printed pp.117–119.
(blueprint: def-sfb-relative-additive-coordinates).

An additive coordinate is a Cartesian affine-line parametrization preserving addition
on every test algebra. This describes a group-scheme isomorphism without choosing a
second group structure on the polynomial affine line.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped MonObj

namespace AlgebraicGeometry.RelativeAdditiveCoordinates

/-- The affine R-line regarded as a scheme over Spec A.
Source: Conrad, Lemma 4.2.2, pp.118–119.
(blueprint: def-sfb-relative-additive-coordinates). -/
def line (A R : Type u) [CommRing A] [CommRing R] [Algebra A R] :
    Over (Spec (.of A)) :=
  (algSpec (.of A)).obj (op (CommAlgCat.of A (Polynomial R)))

/-- Evaluation of the line coordinate at a B-valued element, with coefficients
transported along R → B. Source: Conrad, Lemma 4.2.2, pp.118–119.
(blueprint: def-sfb-relative-additive-coordinates). -/
def point (A R B : Type u) [CommRing A] [CommRing R] [CommRing B]
    [Algebra A R] [Algebra A B] [Algebra R B] [IsScalarTower A R B] (x : B) :
    points (line A R) B :=
  (algSpec (.of A)).map
    (CommAlgCat.ofHom (Polynomial.aevalTower (IsScalarTower.toAlgHom A R B) x)).op

/-- The unit coordinate of a point of the existing Laurent multiplicative group.
Source: Conrad, Lemma 4.2.2, p.118.
(blueprint: def-sfb-relative-additive-coordinates). -/
def unitValue (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (t : points (RingGroupSchemes.multiplicative A).X B) : B :=
  (Spec.homEquiv t.left).hom (LaurentPolynomial.T 1)

/-- A Cartesian parametrization of U_R by the affine R-line preserving its additive
law on all R-algebras. Cartesian means that the induced map to U ×_A Spec R is an
isomorphism; the point identity means it is a group-scheme isomorphism from G_a.
Source: Conrad, Lemma 4.2.2, pp.118–119.
(blueprint: def-sfb-relative-additive-coordinates). -/
def IsAdditiveCoordinate (A : Type u) [CommRing A]
    (U : Over (Spec (.of A))) [GrpObj U]
    (R : Type u) [CommRing R] [Algebra A R] (q : line A R ⟶ U) : Prop :=
  IsPullback q.left
      (Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R)))) U.hom
      (Spec.map (CommRingCat.ofHom (algebraMap A R))) ∧
    ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower A R B]
      (x y : B),
      point A R B (x + y) ≫ q = (point A R B x ≫ q) * (point A R B y ≫ q)

end AlgebraicGeometry.RelativeAdditiveCoordinates
