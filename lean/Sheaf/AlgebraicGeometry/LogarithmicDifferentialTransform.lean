/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.LogarithmicCoefficientIdeal
public import Sheaf.AlgebraicGeometry.MarkedIdealData
public import Sheaf.AlgebraicGeometry.EtaleCoordinateFlag
import Mathlib.RingTheory.Kaehler.Basic
import Sheaf.AlgebraicGeometry.EtaleAtPointFromDifferentials
import Sheaf.RingTheory.RegularSequenceGradedPolynomial
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Etale.Kaehler
import Sheaf.AlgebraicGeometry.ImplicitTaylorCoordinateCalculus
import Sheaf.AlgebraicGeometry.MarkedControlledBlowupCharts
import Sheaf.AlgebraicGeometry.PermissibleCoordinateChart
import Sheaf.RingTheory.SmoothLocalTangentConeExtension
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Kaehler.Polynomial
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.AlgebraicGeometry.SeparableResidueCotangentInjective
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm

/-! # Taylor orders and logarithmic differential transforms

Source: Bierstone--Milman, Functoriality in Resolution of Singularities,
Sections 3.1--3.2, Corollaries 3.4--3.6, Corollary 4.1 and Exercise 4.4(2),
pp. 620--625 (blueprint: lem-trf-logarithmic-differential-transform).

## Main statements

* `taylor_order_criterion`, `order_semicontinuous_bounded`, `order_product_sum`:
  orders of coherent ideals, including infinite orders.
* `order_logDifferential_smooth_pullback`: smooth pullback of both constructions.
* `logDifferential_finite_test`: existence and inclusion along every finite test word.
* `exists_contact_coordinate`, `contact_finite_test`: creation and persistence of contact.

The helpers only extend the existing test relation by open restriction and record the same
support map for transforming ideals with different marks. They introduce no chosen quotient.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.MarkedIdeal
open HilbertSamuel

/-- A test with its canonical map on supports, including open restrictions. The commuting
triangle determines this map because the old support is a closed immersion. For a geometric
test the existing relation supplies its strict or cartesian support and its marked ideal.
Source: BM Definitions 2.2--2.5 and the local convention in Section 3.2
(blueprint: lem-trf-logarithmic-differential-transform). -/
structure DifferentialTestStep (A B : MarkedIdeal.{u}) where
  ambient : B.ambient.Z ⟶ A.ambient.Z
  support : B.marked.N ⟶ A.marked.N
  square : support ≫ A.marked.j = B.marked.j ≫ ambient
  operation : Option (Step A.ambient B.ambient)
  geometry : match operation with
    | some s => s.π = ambient ∧ s.Admissible A.marked.cosupport ∧
        s.Transforms A.marked B.marked
    | none => IsOpenImmersion ambient ∧ ambient ≫ A.ambient.p = B.ambient.p ∧
        B.ambient.boundary = A.ambient.boundary.map (fun D ↦ D.comap ambient) ∧
        IsPullback support B.marked.j A.marked.j ambient ∧
        B.marked.ideal = A.marked.ideal.comap support ∧
        B.marked.marking = A.marked.marking

/-- The transform of an ideal with the specified mark on the same support. Controlled
blowups divide by exactly the indicated exceptional power, expressed as multiplication;
all other operations use ordinary pullback. The operation tag is retained even if the
underlying blowup also admits the other description.
Source: BM Definitions 2.2--2.5, Corollary 3.5
(blueprint: lem-trf-logarithmic-differential-transform). -/
def DifferentialTestStep.TransformsIdeal {A B : MarkedIdeal.{u}}
    (s : DifferentialTestStep A B) (d : ℕ)
    (J : A.marked.N.IdealSheafData) (K : B.marked.N.IdealSheafData) : Prop :=
  match s.operation with
  | some t => if t.kind = .admissibleBlowup then
      K * ((t.center.comap s.ambient).comap B.marked.j) ^ d = J.comap s.support
    else K = J.comap s.support
  | none => K = J.comap s.support

/-- A finite word in the existing tests and open restrictions, including the empty word.
Source: BM Corollary 3.5, with restriction to open charts
(blueprint: lem-trf-logarithmic-differential-transform). -/
structure DifferentialTestSequence (n : ℕ) where
  state : Fin (n + 1) → MarkedIdeal.{u}
  step : ∀ i : Fin n, DifferentialTestStep (state i.castSucc) (state i.succ)

/-- The logarithmic differential construction gives coherent ideals in every degree.
Source: BM Section 3.2, pp. 620--621
(blueprint: lem-trf-logarithmic-differential-transform).

Proof (the coherence input in node step 4): On a smooth coordinate neighbourhood the
logarithmic tangent sheaf has the finite frame consisting of the boundary Euler operators
and the remaining coordinate derivatives. Differentiate finitely many generators of the
coherent ideal with this frame, retaining those generators. Leibniz shows this finite
family generates the first differential ideal. Iterate; localization commutes with these
operators, so the affine ideals of logDifferential glue to precisely these coherent ideals.
This is the coherence assertion of lem-trf-logarithmic-derivative-single-transform.
-/
theorem logDifferential_coherent (A : MarkedIdeal.{u}) (j : ℕ) :
    Scheme.Modules.IsQuasiCoherentFiniteType
      (logDifferential (A.ambient.boundary.map (fun D ↦ D.comap A.marked.j))
        A.marked.ideal j).toModules := by
  sorry

/-- Taylor detects the ordinary order at every scheme point, without requiring a closed
or rational point. Source: BM Lemma 3.2(3), pp. 621--622
(blueprint: lem-trf-logarithmic-differential-transform).

Proof (node steps 1--3): Smooth local rings are regular. Regular parameters form a regular
sequence (lem-weil-pbc-regular-local-generators-regular-sequence), and their associated graded
ring is the residue-field polynomial ring (lem-pur-regular-sequence-graded-polynomial).
The residue field is finitely generated and separably generated over Q by the two field
lemmas. The cotangent injection and locally free smooth differentials give local derivations
whose values on these parameters are the coordinate Kronecker symbols modulo the maximal
ideal. Each derivation lowers maximal-ideal powers by at most one. Conversely a germ outside
the q-th power has a nonzero initial homogeneous form of degree s < q. Apply an ordered
s-fold coordinate derivative: its residue is a nonzero coefficient times a multi-factorial.
Leibniz kills all other terms, including differentiated coefficients. Characteristic zero
makes the factorial invertible. No commutation of the chosen derivations is needed.
-/
theorem taylor_order_criterion (A : MarkedIdeal.{u}) (x : A.marked.N)
    (q : ℕ) (hq : 1 ≤ q) :
    (q : ℕ∞) ≤ order A.marked.ideal x ↔
      stalkIdeal (logDifferential [] A.marked.ideal (q - 1)) x ≤
        IsLocalRing.maximalIdeal (A.marked.N.presheaf.stalk x) := by
  sorry

/-- Closed order thresholds and the nonzero-component finiteness assertions.
Source: BM Section 3.2 and the Taylor-order consequences of Lemma 3.2(3)
(blueprint: lem-trf-logarithmic-differential-transform).

Proof (node step 4): Coherence of differential ideals is supplied by
lem-trf-logarithmic-derivative-single-transform. Taylor identifies each positive order
threshold with the zero locus of a coherent differential ideal; the zero threshold is all
of N. If a stalk is zero, finite generation makes the ideal zero on a neighbourhood,
contradicting nonvanishing at the generic point of a component through it. Apply
lem-weil-pbc-krull-intersection-jacobson to the maximal ideal and the finite module R:
a nonzero germ has finite order. The open complement of the next order threshold gives a
local bound. Quasi-compactness supplies finitely many such bounds and hence a finite image.
-/
theorem order_semicontinuous_bounded (A : MarkedIdeal.{u}) :
    (∀ q : ℕ, IsClosed {x : A.marked.N | (q : ℕ∞) ≤ order A.marked.ideal x}) ∧
    ((∀ C ∈ irreducibleComponents A.marked.N, ∀ η : A.marked.N,
        IsGenericPoint η C → stalkIdeal A.marked.ideal η ≠ ⊥) →
      (∀ x : A.marked.N, ∃ (U : A.marked.N.Opens) (b : ℕ),
        x ∈ U ∧ ∀ y ∈ U, order A.marked.ideal y ≤ (b : ℕ∞)) ∧
      (Set.range (order A.marked.ideal)).Finite) := by
  sorry

/-- Products add orders and sums take their minimum, in the extended natural numbers.
Source: BM Section 3.2, Taylor-order consequences and the regular graded-ring calculation
(blueprint: lem-trf-logarithmic-differential-transform).

Proof (node steps 1 and 5): The order of a finitely generated stalk ideal is the minimum
of its generator orders. The initial forms of generators attaining the minima multiply to
a nonzero form in the graded polynomial domain. Every generator product has at least the
sum order, and this product attains it. Zero stalk ideals give infinity. Containment of a
sum in any maximal-ideal power is equivalent to containment of both summands, giving the
minimum, including unit and zero ideals.
-/
theorem order_product_sum (A : MarkedIdeal.{u}) (J : A.marked.N.IdealSheafData)
    (hJ : Scheme.Modules.IsQuasiCoherentFiniteType J.toModules) (x : A.marked.N) :
    order (A.marked.ideal * J) x = order A.marked.ideal x + order J x ∧
    order (A.marked.ideal + J) x = min (order A.marked.ideal x) (order J x) := by
  sorry

/-- Smooth pullback preserves orders and all logarithmic differential ideals. Relative
coordinate directions are included; neither residue fields nor relative dimensions are fixed.
Source: BM Lemma 3.2(4), pp. 621--622
(blueprint: lem-trf-logarithmic-differential-transform).

Proof (node step 6): The affine smooth-ring comparison identifies the map of local rings as
essentially smooth. By lem-trf-smooth-local-tangent-cone-extension its graded map is a scalar
extension followed by a polynomial extension, hence injective. A generator attaining the
minimum order keeps its nonzero initial form. Zero ideals and unit ideals are immediate.
For differential ideals use the smooth-pullback clause of
lem-trf-logarithmic-derivative-single-transform, including relative derivations and split
boundary components; iterate it for each j.
-/
theorem order_logDifferential_smooth_pullback (A : MarkedIdeal.{u})
    {Y : Scheme.{u}} (g : Y ⟶ A.marked.N) [Smooth g]
    [QuasiCompact (g ≫ A.marked.j ≫ A.ambient.p)] :
    (∀ y : Y, order (A.marked.ideal.comap g) y = order A.marked.ideal (g y)) ∧
    ∀ j : ℕ,
      logDifferential (A.ambient.boundary.map (fun D ↦ (D.comap A.marked.j).comap g))
          (A.marked.ideal.comap g) j =
        (logDifferential (A.ambient.boundary.map (fun D ↦ D.comap A.marked.j))
          A.marked.ideal j).comap g := by
  sorry

/-- Every finite test word transforms the differential ideal with the lowered mark;
its transform is contained in the differential ideal of the transformed original.
Source: BM Corollaries 3.4--3.6, pp. 622--623
(blueprint: lem-trf-logarithmic-differential-transform).

Proof (node step 7): Induct on the finite word. The zero-length inclusion is equality.
Order loss in lem-trf-logarithmic-derivative-single-transform makes every cosupport center
permissible for the derivative ideal and its smaller transformed subideal. Apply that lemma
at the next stage. Ordinary pullback preserves inclusion. For a controlled blowup,
lem-trf-marked-controlled-blowup-charts gives regular controlled transforms; smoothness
and lem-weil-pbc-smooth-scheme-over-field-regular, followed by lem-sc-regular-local-domain,
make the exceptional coordinate a nonzerodivisor. Cancel its (d-j)-th power to preserve
inclusion after division. Compose the two inclusions. Open restrictions, line products and
exceptional-intersection tests use ordinary pullback. Empty strict transforms are allowed.
-/
theorem logDifferential_finite_test {n : ℕ} (T : DifferentialTestSequence.{u} n)
    (j : ℕ) (hj : j < (T.state 0).marked.marking) :
    ∃ J : ∀ i : Fin (n + 1), (T.state i).marked.N.IdealSheafData,
      J 0 = logDifferential
        ((T.state 0).ambient.boundary.map (fun D ↦ D.comap (T.state 0).marked.j))
        (T.state 0).marked.ideal j ∧
      (∀ i : Fin n, (T.step i).TransformsIdeal ((T.state i.castSucc).marked.marking - j)
        (J i.castSucc) (J i.succ)) ∧
      ∀ i : Fin (n + 1), J i ≤ logDifferential
        ((T.state i).ambient.boundary.map (fun D ↦ D.comap (T.state i).marked.j))
        (T.state i).marked.ideal j := by
  sorry

/-- A pure coordinate derivative supplies local maximal contact at a point of finite
positive order when the boundary is empty. Source: BM Exercise 4.4(2), p. 625
(blueprint: lem-trf-logarithmic-differential-transform).

Proof (node step 8): Choose a generator f attaining the order d and an étale coordinate
chart (sbc-thm-etale-local-normal-form). The centered Taylor map of
lem-trf-implicit-taylor-coordinate-calculus has a nonzero degree-d form P, by the Taylor
criterion above. Coordinate derivations span by the polynomial differential basis and
formally étale differential base change. A nonzero polynomial over any extension of Q
cannot vanish on all rational vectors; choose v with P(v) nonzero and make it a coordinate
by a rational linear change. Then the d-th pure derivative is d! P(v), a unit after
shrinking. Its preceding derivative vanishes at x and has invertible differential.
lem-pur-etale-at-point-from-differentials makes its zero locus a smooth hypersurface.
For d=1 it is f itself; dimension zero admits no positive finite order.
-/
theorem exists_contact_coordinate (A : MarkedIdeal.{u})
    (hE : A.ambient.boundary = []) (x : A.marked.N)
    (hx : order A.marked.ideal x = (A.marked.marking : ℕ∞)) :
    ∃ (U : A.marked.N.affineOpens) (hxU : x ∈ U.1) (r : ℕ)
      (v : Fin r → Γ(U.1.toScheme, ⊤)) (a : Fin r)
      (D : Derivation ℤ Γ(U.1.toScheme, ⊤) Γ(U.1.toScheme, ⊤))
      (f : Γ(U.1.toScheme, ⊤)),
      Etale (AffineSpace.homOfVector (U.1.ι ≫ A.marked.j ≫ A.ambient.p)
        (fun k : ULift.{u} (Fin r) ↦ v k.down)) ∧
      (∀ b : Fin r, D (v b) = if b = a then 1 else 0) ∧
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {f}) ≤ A.marked.ideal.comap U.1.ι ∧
      IsUnit ((D : _ → _)^[A.marked.marking] f) ∧
      order (Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {((D : _ → _)^[A.marked.marking - 1] f)})) ⟨x, hxU⟩ = 1 ∧
      Smooth ((Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {((D : _ → _)^[A.marked.marking - 1] f)})).subschemeι ≫
          U.1.ι ≫ A.marked.j ≫ A.ambient.p) := by
  sorry

/-- Mark-one transforms of a transverse contact section remain contact near transformed
cosupport, and their local equations retain order one and transversality.
Source: BM Corollary 4.1, pp. 624--625
(blueprint: lem-trf-logarithmic-differential-transform).

Proof (node steps 9--12): The single-transform order-loss bound makes h vanish on cosupport.
Apply the finite-test derivative inclusion with j=d-1; the transform of (h) is contained in
the transformed differential ideal. At each stage the same bound puts cosupport in V(h_t).
A smooth center inside that zero locus lies there scheme-theoretically: its regular local
domains inject into their generic fraction fields (smooth regularity and
lem-sc-regular-local-domain). In simultaneous coordinates replace a nonboundary center
coordinate by h_t, using its unit coefficient and the étale differential criterion.
The controlled chart theorem gives h_t/e as a nonboundary coordinate on every surviving
chart. The h_t-pivot chart has transform 1 and empty cosupport, so discard it. For a
boundary-intersection blowup h_t is an independent unchanged coordinate; ordinary pullback
also handles lines and opens. The permissible-coordinate-chart lemma preserves the
boundary independence. Induct over the word and shrink near cosupport. All statements are
vacuous on empty supports and discarded charts.
-/
theorem contact_finite_test {n : ℕ} (T : DifferentialTestSequence.{u} n)
    (h : Γ((T.state 0).marked.N, ⊤))
    (hmem : Scheme.IdealSheafData.ofIdealTop (Ideal.span {h}) ≤
      logDifferential
        ((T.state 0).ambient.boundary.map (fun D ↦ D.comap (T.state 0).marked.j))
        (T.state 0).marked.ideal ((T.state 0).marked.marking - 1))
    (horder : ∀ x ∈ (Scheme.IdealSheafData.ofIdealTop (Ideal.span {h})).support,
      order (Scheme.IdealSheafData.ofIdealTop (Ideal.span {h})) x = 1)
    (htransverse : HasEtaleCoordinateFlag ((T.state 0).marked.j ≫ (T.state 0).ambient.p)
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {h}))
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {h}))
      ((T.state 0).ambient.boundary.map (fun D ↦ D.comap (T.state 0).marked.j))) :
    ∃ K : ∀ i : Fin (n + 1), (T.state i).marked.N.IdealSheafData,
      K 0 = Scheme.IdealSheafData.ofIdealTop (Ideal.span {h}) ∧
      (∀ i : Fin n, (T.step i).TransformsIdeal 1 (K i.castSucc) (K i.succ)) ∧
      ∀ i : Fin (n + 1),
        K i ≤ logDifferential
          ((T.state i).ambient.boundary.map (fun D ↦ D.comap (T.state i).marked.j))
          (T.state i).marked.ideal ((T.state i).marked.marking - 1) ∧
        (T.state i).cosupport ⊆ (K i).support ∧
        ∀ x ∈ (T.state i).cosupport, ∃ U : (T.state i).marked.N.Opens,
          x ∈ U ∧ ((K i).comap U.ι).IsInvertible ∧
          (∀ y ∈ ((K i).comap U.ι).support, order ((K i).comap U.ι) y = 1) ∧
          HasEtaleCoordinateFlag (U.ι ≫ (T.state i).marked.j ≫ (T.state i).ambient.p)
            ((K i).comap U.ι) ((K i).comap U.ι)
            ((T.state i).ambient.boundary.map
              (fun D ↦ (D.comap (T.state i).marked.j).comap U.ι)) := by
  sorry

end AlgebraicGeometry.MarkedIdeal
