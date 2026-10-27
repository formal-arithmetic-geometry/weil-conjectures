module

public import Sheaf.AlgebraicGeometry.BinomialGeometricFibres
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Gluing three arithmetic nodal charts

Source: Stacks Project, curves.tex, Tags 0C59 and 0C5A, and the explicit three-chart
calculation in the proof of de Jong, Lemma 3.13, p.609
(blueprint: lem-sfb-nodal-three-chart-gluing).

The coordinate rings and coordinate classes are the published `BinomialPlaneCurve`
constructions. The helpers merely restrict these coordinates to the actual intersections.
The overlap equations are ring identities, so they make sense also when n=2 and y=0.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.NodalThreeChart

open BinomialPlaneCurve

/-- A left chart coordinate restricted to the scheme-theoretic intersection.
Source: the three-chart calculation, de Jong Lemma 3.13, p.609
(blueprint: lem-sfb-nodal-three-chart-gluing). -/
def left {R : Type u} [CommRing R] {a b : R} {Z : Scheme.{u}}
    (i : curve R a ⟶ Z) (j : curve R b ⟶ Z) (k : Fin 2) :
    Γ(pullback i j, ⊤) :=
  (pullback.fst i j).appTop.hom
    ((Scheme.ΓSpecIso (.of (Ring R a))).inv.hom (coord R a k))

/-- A right chart coordinate restricted to the same intersection.
Source: the three-chart calculation, de Jong Lemma 3.13, p.609
(blueprint: lem-sfb-nodal-three-chart-gluing). -/
def right {R : Type u} [CommRing R] {a b : R} {Z : Scheme.{u}}
    (i : curve R a ⟶ Z) (j : curve R b ⟶ Z) (k : Fin 2) :
    Γ(pullback i j, ⊤) :=
  (pullback.snd i j).appTop.hom
    ((Scheme.ΓSpecIso (.of (Ring R b))).inv.hom (coord R b k))

/-- A coefficient restricted from the left chart to the intersection.
The hypotheses identifying the structure maps identify this with the right coefficient.
Source: the three-chart calculation, de Jong Lemma 3.13, p.609
(blueprint: lem-sfb-nodal-three-chart-gluing). -/
def scalar {R : Type u} [CommRing R] {a b : R} {Z : Scheme.{u}}
    (i : curve R a ⟶ Z) (j : curve R b ⟶ Z) (c : R) :
    Γ(pullback i j, ⊤) :=
  (pullback.fst i j).appTop.hom
    ((Scheme.ΓSpecIso (.of (Ring R a))).inv.hom (algebraMap R (Ring R a) c))

/-- Flatness, nodal geometric fibres, the generic Laurent line, and regularity of the
three-chart gluing. Coordinates 0,1 are respectively x,t on ix; r,s on im; y,h on iy.
The overlap identities express precisely the reciprocal transitions, including their
symmetric inverse. In particular h*(x^(n-2)*t^(n-1))=1 is the everywhere-defined
version of h=pi/y; it remains meaningful on the exponent-two special fibre.
Source: Stacks Project, curves.tex, Tags 0C59 and 0C5A; explicit three-chart gluing
from inherited step 9 of de Jong Lemma 3.13, p.609
(blueprint: lem-sfb-nodal-three-chart-gluing).

Proof:
1. Apply lem-sfb-dvr-binomial-local-geometry with exponent 1 on the outer charts
   and exponent n-2 on the middle chart when n>=3. Transfer ring flatness to stalks
   by lem-weil-pbc-affine-open-stalk-localization and
   lem-weil-pbc-flat-map-local-criterion. When n=2 the middle chart lies in ix,
   since rs=1. The finite two-generator, one-relation presentations give local
   finite presentation on all three charts.
2. By lem-sc-dvr-dimension-one the image of a geometric point is generic or closed.
   The affine fibre-product formula gives equations xt=a, rs=a^(n-2), yh=a over
   the algebraically closed field, and pulls back the same principal overlaps.
3. Apply lem-sfb-binomial-geometric-fibres: each chart is nonempty, connected,
   reduced, of dimension one, and smooth except at its crossing. Reducedness is
   local. Use lem-weil-pbc-dimension-bound-open-cover and scheme sobriety for the
   upper dimension bound; an axis chain gives the lower bound. At each crossing,
   lem-sfb-monomial-local-completion with ideal (uv) identifies the completed
   local ring with Omega[[u,v]]/(uv).
4. The intersections D(t)=D(r) and D(h)=D(s) are nonempty over every algebraically
   closed extension. The three connected charts thus have connected union; the
   outer-to-outer intersection need not be nonempty on the special fibre.
5. Over Frac(R), pi is invertible; each middle or right point belongs to ix.
   Thus the generic fibre is ix over Frac(R), namely the Laurent line.
6. The exponent-one outer charts are regular. For n=3 the middle exponent is one.
   For n>=4, the DVR binomial local-geometry lemma makes the middle chart regular
   away from (pi,r,s). For n=2, rs=1 is Laurent and smooth: its presentation has
   a unit Jacobian derivative, by lem-weil-pbc-standard-smooth-is-smooth and
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine. It lies in the outer chart,
   so Z is regular also in this case. All computations allow every characteristic.
-/
theorem gluing (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (n : ℕ) (hn : 2 ≤ n) (Z : Scheme.{u}) (f : Z ⟶ Spec (.of R))
    (ix : curve R π ⟶ Z) (im : curve R (π ^ (n - 2)) ⟶ Z) (iy : curve R π ⟶ Z)
    [IsOpenImmersion ix] [IsOpenImmersion im] [IsOpenImmersion iy]
    (hcover : Set.range ix ∪ Set.range im ∪ Set.range iy = Set.univ)
    (hx : ix ≫ f = toField R π)
    (hm : im ≫ f = toField R (π ^ (n - 2)))
    (hy : iy ≫ f = toField R π)
    (hxm : ix ⁻¹' Set.range im = (PrimeSpectrum.basicOpen (coord R π 1)).carrier)
    (hmx : im ⁻¹' Set.range ix =
      (PrimeSpectrum.basicOpen (coord R (π ^ (n - 2)) 0)).carrier)
    (hym : iy ⁻¹' Set.range im = (PrimeSpectrum.basicOpen (coord R π 1)).carrier)
    (hmy : im ⁻¹' Set.range iy =
      (PrimeSpectrum.basicOpen (coord R (π ^ (n - 2)) 1)).carrier)
    (hxy : ix ⁻¹' Set.range iy =
      (PrimeSpectrum.basicOpen (coord R π 0 ^ (n - 2) * coord R π 1 ^ n)).carrier)
    (hyx : iy ⁻¹' Set.range ix =
      (PrimeSpectrum.basicOpen (coord R π 0 ^ (n - 2) * coord R π 1 ^ n)).carrier)
    (htr : left ix im 1 * right ix im 0 = 1)
    (hs : right ix im 1 = left ix im 0 ^ (n - 2) * left ix im 1 ^ (n - 1))
    (hxr : left ix im 0 = scalar ix im π * right ix im 0)
    (hhs : left iy im 1 * right iy im 1 = 1)
    (hr : right iy im 0 = left iy im 0 ^ (n - 2) * left iy im 1 ^ (n - 1))
    (hys : left iy im 0 = scalar iy im π * right iy im 1)
    (hyy : right ix iy 0 = left ix iy 0 ^ (n - 1) * left ix iy 1 ^ n)
    (hh : right ix iy 1 * (left ix iy 0 ^ (n - 2) * left ix iy 1 ^ (n - 1)) = 1)
    (hxx : left ix iy 0 = right ix iy 0 ^ (n - 1) * right ix iy 1 ^ n)
    (ht : left ix iy 1 * (right ix iy 0 ^ (n - 2) * right ix iy 1 ^ (n - 1)) = 1) :
    Flat f ∧
    (∃ hfp : LocallyOfFinitePresentation f,
      @HasNodalGeometricFibres _ _ f hfp ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of R)),
        IsReduced (pullback f g)) ∧
    (∃ e : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) ≅
        Spec (.of (LaurentPolynomial (FractionRing R))),
      e.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (FractionRing R) (LaurentPolynomial (FractionRing R)))) =
          pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) ∧
    IsRegularScheme (curve R π) ∧
    (∀ z : Z, ¬ IsRegularLocalRing (Z.presheaf.stalk z) →
      4 ≤ n ∧ ∃ o : curve R (π ^ (n - 2)),
        o.asIdeal = Ideal.span
          {algebraMap R (Ring R (π ^ (n - 2))) π,
            coord R (π ^ (n - 2)) 0, coord R (π ^ (n - 2)) 1} ∧ im o = z) ∧
    (n = 2 → Smooth (toField R (π ^ (n - 2))) ∧
      (∃ e : curve R (π ^ (n - 2)) ≅ Spec (.of (LaurentPolynomial R)),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (LaurentPolynomial R))) =
          toField R (π ^ (n - 2))) ∧ IsRegularScheme Z) ∧
    (n = 3 → IsRegularScheme (curve R (π ^ (n - 2))) ∧ IsRegularScheme Z) := by
  sorry

end AlgebraicGeometry.NodalThreeChart
