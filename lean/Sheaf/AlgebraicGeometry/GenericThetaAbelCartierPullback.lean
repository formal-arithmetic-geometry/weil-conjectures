module

public import Sheaf.AlgebraicGeometry.SymmetricAbelImageGeometry
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.DivisorModule
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
import WeilConjectures.AlgebraicGeometry.Hilbert.Curve
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.BirationalGenericIsomorphismOpen
import WeilConjectures.AlgebraicGeometry.DensePoints
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import WeilConjectures.AlgebraicGeometry.GenericFlatness
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatAffineBasis
import Sheaf.AlgebraicGeometry.DivisorLineBundleAgreesSC

/-! # Generic Cartier pullback of the translated negative theta divisor

Source: Milne, Abelian Varieties, III, Lemma 6.7, printed pp. 105–106
(blueprint: lem-sfb-generic-theta-abel-cartier-pullback).

The Abel morphisms are specified on families using the fixed Picard representation.
Equality of ideal sheaves records equality of closed subschemes, including multiplicities.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonObj
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The family formula D ↦ [O(D-rP)] for the Abel map of a represented Hilbert functor.
Here N represents O(-P). This packages the formula already supplied by the Abel-image
geometry statement, without choosing a new Hilbert scheme or Picard representation.
Source: Milne III, Section 5, Theorem 5.1
(blueprint: lem-sfb-generic-theta-abel-cartier-pullback). -/
def IsPointedHilbertAbelMap
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    (J : Over (Spec (.of k))) (eJ : (picardFunctorDegree f 0).obj.RepresentableBy J)
    (N : C.Pic) (r : ℕ) (H : Over (Spec (.of k)))
    (eH : (hilbertPresheaf f r).RepresentableBy H) (a : H ⟶ J) : Prop :=
  ∀ (T : Over (Spec (.of k))) (d : T ⟶ H),
    ∃ (L : (pullback f T.hom).Pic),
      Nonempty ((fromSkeleton _).obj L.val ≅ (eH.homEquiv d).val.toModulesᵛ) ∧
      ∃ hL : L * Scheme.Pic.map (pullback.fst f T.hom) (N ^ r) ∈
          (picardSubfunctorDegree f 0).obj (op T),
        eJ.homEquiv (d ≫ a) =
          (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
            (picardSubfunctorDegree f 0).toFunctor).app (op T)
              ⟨L * Scheme.Pic.map (pullback.fst f T.hom) (N ^ r), hL⟩

/-- The ideal of Theta^-+a is the inverse image of the theta ideal under x ↦ a-x.
The morphism is t_(-a) followed by inversion, so its inverse image is exactly
`t_(-a)^* ([-1]^* Theta)`, with the translation convention in the node.
Source: Milne III, Section 6, notation before Theorem 6.6
(blueprint: lem-sfb-generic-theta-abel-cartier-pullback). -/
def translatedNegativeThetaIdeal
    {k : Type u} [Field k] (J : Over (Spec (.of k))) [GrpObj J]
    (I : J.left.IdealSheafData) (a : Over.mk (𝟙 (Spec (.of k))) ⟶ J) :
    J.left.IdealSheafData :=
  I.comap ((CartesianMonoidalCategory.lift (𝟙 J) (Over.homMk J.hom ≫ a ≫ ι[J]) ≫ μ[J] ≫ ι[J]).left)

/-- On a dense open of the Jacobian, the unique degree-g Abel divisor is reduced and
is exactly the Cartier inverse image of the translated negative theta divisor.
Source: Milne III, Lemma 6.7, printed pp. 105–106
(blueprint: lem-sfb-generic-theta-abel-cartier-pullback).

Proof:
1. Smooth-connected-curve-local-rings, projective-proper and geometric integrality make
   C integral and proper. Hilb-curves and Hilb-geometrically-integral make the Hilbert
   schemes smooth proper integral varieties. Abel-image-geometry gives the integral
   Cartier theta image and birationality of the degree-g and degree-(g-1) Abel maps.
   Abelian-variety-characterization and smooth-regular make J integral and Noetherian.
2. Integral-pullback-geometric-flat-open makes C times H_(g-1) and C times Theta integral.
   Proper-base-change, proper-composition and proper-over-separated make their maps
   proper. The image maps are surjective by proper-closed-image and birational density;
   surjective-base-change applies to their base changes.
3. Birational-generic-isomorphism-open supplies full isomorphism loci for the two Abel
   maps. In particular a degree-g divisor is unique over a dense open of J, and the map
   C times H_(g-1) to C times Theta is birational.
4. Remove the proper image of (Q,E) ↦ 2Q+E, using Hilb-addition. Rational-points-dense
   supplies g distinct points, so the remaining open of reduced degree-g divisors is
   nonempty. Lft-over-field-jacobson-space and closed-point-residue-field-base identify
   this image with precisely the repeated-point locus. For g=1 every divisor is reduced.
5. Hilb-addition identifies the composite to J with the degree-g Abel map after addition.
   Its rank is g. Surjective-base-change shows that the generic incidence fibre is finite.
6. Generic-finite-morphism-open-neighborhood and generic-flatness shrink the incidence
   map to finite flat. Finite-flat-affine-basis makes it free of rank n. Integral-function-
   field-affine-fraction identifies n with its function field degree; the birational
   comparison in step 3 and the addition rank in step 5 give n=g.
7. Intersect this open with the reduced-divisor part of the degree-g isomorphism locus.
   The intersection U is dense and open. Its unique D(a) has g distinct points, and the
   incidence fibre E_a has vector space dimension g.
8. The fibre-product universal property identifies E_a with fP^(-1)(Theta^-+a) as a
   closed subscheme. The surjective base change of the Hilbert-image map identifies its
   support with exactly the g points of D(a), using the Hilbert addition formula.
9. Evaluation of its finite algebra at those g rational points is surjective by separating
   the distinct maximal ideals. Equal dimensions make it an isomorphism, so E_a is
   reduced. The DVR local rings identify its ideal with the product of the g point ideals.
   Inversion and translation preserve Cartier equations, so the translated theta is
   Cartier too. This proves equality of effective Cartier divisors with multiplicities.
10. Pull back each local Cartier equation and its dual basis. Unit transition functions
    agree, so these identifications glue to the line bundle isomorphism. The divisor-
    line-bundle-agrees-sc comparison identifies the result with the curve's O_C(D(a)).
-/
theorem exists_dense_open_genericThetaAbelCartierPullback
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsHProjective f]
    (g : ℕ) (hg : f.genus = g) (hgpos : 1 ≤ g)
    (P : Spec (.of k) ⟶ C) (hP : P ≫ f = 𝟙 _)
    (J : Over (Spec (.of k))) [GrpObj J]
    (hJ : @IsJacobian k _ C f _ _ _ (pointedAbelGeometricIntegrality f) J _)
    (eJ : (picardFunctorDegree f 0).obj.RepresentableBy J)
    (heJ : IsPicardZeroMul f eJ)
    (N : C.Pic) (hN : Nonempty ((fromSkeleton C.Modules).obj N.val ≅ P.ker.toModules))
    (fP : Over.mk f ⟶ J)
    (hfP : ∀ (T : Over (Spec (.of k))) (Q : T ⟶ Over.mk f),
      ∃ (LQ : (pullback f T.hom).Pic),
        Nonempty ((fromSkeleton _).obj LQ.val ≅
          (pullback.lift Q.left (𝟙 T.left) Q.w).ker.toModulesᵛ) ∧
        ∃ hQ : LQ * Scheme.Pic.map (pullback.fst f T.hom) N ∈
            (picardSubfunctorDegree f 0).obj (op T),
          eJ.homEquiv (Q ≫ fP) =
            (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
              (picardSubfunctorDegree f 0).toFunctor).app (op T)
                ⟨LQ * Scheme.Pic.map (pullback.fst f T.hom) N, hQ⟩)
    (H₀ : Over (Spec (.of k))) (e₀ : (hilbertPresheaf f (g - 1)).RepresentableBy H₀)
    (a₀ : H₀ ⟶ J) (ha₀ : IsPointedHilbertAbelMap f J eJ N (g - 1) H₀ e₀ a₀)
    (H : Over (Spec (.of k))) (eH : (hilbertPresheaf f g).RepresentableBy H)
    (aG : H ⟶ J) (haG : IsPointedHilbertAbelMap f J eJ N g H eH aG) :
    ∃ U : J.left.Opens, Dense (U : Set J.left) ∧
      ∀ a : Over.mk (𝟙 (Spec (.of k))) ⟶ J,
        Set.range a.left ⊆ U →
        (∃! d : Over.mk (𝟙 (Spec (.of k))) ⟶ H, d ≫ aG = a) ∧
        ∀ d : Over.mk (𝟙 (Spec (.of k))) ⟶ H, d ≫ aG = a →
          ∃ D : C.Divisor,
            0 ≤ D ∧ Scheme.Divisor.degree C D = (g : ℤ) ∧
            (∃ p : Fin g → closedPoints C, Function.Injective p ∧
              D = ∑ i : Fin g, Finsupp.single (p i) 1) ∧
            (eH.homEquiv d).val.comap (inv (pullback.fst f (𝟙 _))) =
              D.prod (fun q n ↦
                Scheme.IdealSheafData.vanishingIdeal ⟨{q.val}, q.prop⟩ ^ n.toNat) ∧
            (translatedNegativeThetaIdeal J a₀.left.ker a).IsInvertible ∧
            ((translatedNegativeThetaIdeal J a₀.left.ker a).comap fP.left).IsInvertible ∧
            (translatedNegativeThetaIdeal J a₀.left.ker a).comap fP.left =
              D.prod (fun q n ↦
                Scheme.IdealSheafData.vanishingIdeal ⟨{q.val}, q.prop⟩ ^ n.toNat) ∧
            Nonempty ((Scheme.Modules.tensorPullback fP.left).obj
              (translatedNegativeThetaIdeal J a₀.left.ker a).toModulesᵛ ≅
                D.moduleOfSmoothConnectedCurve k C f) := by
  sorry

end AlgebraicGeometry
