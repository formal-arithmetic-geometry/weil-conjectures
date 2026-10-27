module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
public import WeilConjectures.AlgebraicGeometry.Hilbert.Curve
public import Sheaf.AlgebraicGeometry.HilbertToPicardMorphism
public import Sheaf.AlgebraicGeometry.DivisorModule
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.AlgebraicGeometry.Birational.Birational
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import Sheaf.AlgebraicGeometry.DivisorLineBundleAgreesSC
import WeilConjectures.AlgebraicGeometry.Hilbert.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.DivisorClassCurve
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
import Sheaf.TraceFormula.ReducedSchemeImage
import Sheaf.AlgebraicGeometry.CotangentSurjectiveOfTangentInjective
import Sheaf.AlgebraicGeometry.RationalUnramifiedCotangentCriterion
import Sheaf.AlgebraicGeometry.UnramifiedLocusBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteUnramifiedOnePointClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.HilbertToPicardSurjective
import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.KrullDimension

/-! # Pointed Abel morphisms and their scheme-theoretic images

Source: Milne, Abelian Varieties, Chapter III, Theorems 1.6–1.7, Lemma 1.8,
Proposition 2.3, Theorem 5.1(a), and Section 6 before Theorem 6.6
(blueprint: lem-sfb-symmetric-abel-image-geometry).

## Main statements

- `exists_pointedAbel_image_geometry`: the family, Abel embedding and all divisor images.

The Picard group records isomorphism classes of actual invertible modules. Normalization
along P records rigidification classes; the universal equality of structure sheaves in
Picard splitting identifies these with classes of rigidified pairs, for arbitrary bases.
The degree-component isomorphism below is specified on every presheaf class. Birationality
is a partial isomorphism whose underlying map agrees with the factor through the image.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonObj
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- Geometric integrality supplied by smoothness and connectedness over the algebraically
closed field; this supplies the instance required by the existing Jacobian interface,
without adding a hypothesis. Source: Milne III, Section 1; prop-pc-xk-integral
(blueprint: lem-sfb-symmetric-abel-image-geometry). -/
abbrev pointedAbelGeometricIntegrality {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] :
    GeometricallyIntegral f :=
  @GeometricallyIntegral.of_isSepClosed k _ C ⟨f⟩ _ ‹Smooth f›
    (IsConnectedCurve.connectedSpace' f)

/-- The normalized universal Picard family and the geometry of all pointed Abel maps.
Source: Milne III, Theorems 1.6–1.7, Lemma 1.8, Proposition 2.3, Theorem 5.1(a),
and Section 6 before Theorem 6.6 (blueprint: lem-sfb-symmetric-abel-image-geometry).

Proof:
1. Projective-proper and smooth-connected-curve-local-rings make C proper and integral;
   prop-pc-xk-integral makes it geometrically integral. Picard splitting
   (sk-prop-picard-pic-split), including its universal structure-sheaf equality, identifies
   the fixed representation with normalized degree-zero classes on every base. Evaluate
   at the identity of J to get M. Naturality gives its pullback classification; compatibility
   with the group law gives the trivial fibre at the origin.
2. thm-pc-hilb-curves represents effective degree-r divisors. Tensoring with O(-rP)
   gives the degree-component isomorphism (prop-pd-picard-degree-decomposition). Compose
   it with lem-sc-hilb-to-pic-morphism. The divisor line bundle agrees with the rational
   function construction by lem-pc-divisor-line-bundle-agrees-sc. The degree-one Hilbert
   functor is C: a finite flat rank-one subscheme is the graph of a unique section;
   conversely graphs are closed by proper-base-change and section-separated-closed-immersion.
3. A fibre consists of the complete linear system of its divisor, by divisor-class-curve
   and global-functions. If h0(O(D))=1 its entire fibre is a singleton: closed-point-residue-
   field-base and lft-over-field-jacobson-space upgrade the rational-point assertion.
   lem-sfb-abel-differential-boundary also makes its tangent map injective.
4. Proper-over-separated makes each Abel map proper. Reduced-scheme-image makes its
   scheme-theoretic image reduced and irreducible, hence integral, also for r=0.
5. Proper-finite-fibre-finite-near gives finiteness near a singleton fibre. Cotangent-
   surjective-of-tangent-injective and rational-unramified-cotangent-criterion give
   unramifiedness at D. Remove the proper image of the complement of the unramified locus;
   finite-unramified-one-point-closed then gives a closed immersion over a neighbourhood.
6. lem-sfb-small-degree-divisor-sections applies at every degree-one divisor. The preceding
   neighbourhoods and the complement of the proper image cover J, by the Jacobson and
   closed-point residue-field lemmas. Closed-finite-etale-zariski-local proves fP closed.
7. For every r <= g the same small-degree lemma supplies a divisor with h0=1. Scheme-image-
   restrict-open identifies its neighbourhood image with an open of W_r. The resulting
   isomorphism of nonempty opens gives birationality of the actual image factor map.
   Dimension-locally-algebraic and the Hilbert dimension give dim W_r = r, including r=0.
8. Hilb-to-pic-surjective in degree g, followed by the translation isomorphism, is surjective.
   Smooth-scheme-over-field-regular and regular-connected-integral make J reduced and
   integral; reduced-scheme-image therefore gives W_g=J as schemes.
9. The integral W_(g-1) has codimension one in the regular integral g-dimensional J.
   Scheme-stalk-dimension-generalization-chains computes its generic local ring dimension:
   a chain of length g-1 inside W followed by two strict generalizations would contradict
   dim J=g; one generalization exists since W is proper. Apply
   lem-per-regular-prime-divisor-local-equations to obtain its effective Cartier ideal.
   When g=1 this is the reduced origin Cartier divisor; no positive-degree case was assumed.
-/
theorem exists_pointedAbel_image_geometry
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsHProjective f]
    (g : ℕ) (hg : f.genus = g) (hgpos : 1 ≤ g)
    (P : Spec (.of k) ⟶ C) (hP : P ≫ f = 𝟙 _)
    (J : Over (Spec (.of k))) [GrpObj J]
    (hJ : @IsJacobian k _ C f _ _ _ (pointedAbelGeometricIntegrality f) J _)
    (eJ : (picardFunctorDegree f 0).obj.RepresentableBy J)
    (heJ : IsPicardZeroMul f eJ) :
    ∃ (M : (pullback f J.hom).Pic)
      (hM : M ∈ (picardSubfunctorDegree f 0).obj (op J)),
      M ∈ (picardFunctorNormalized f P hP).obj (op J) ∧
      eJ.homEquiv (𝟙 J) =
        (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
          (picardSubfunctorDegree f 0).toFunctor).app (op J) ⟨M, hM⟩ ∧
      Scheme.Pic.map (baseChangeMap f η[J]) M = 1 ∧
      (∀ (T : Over (Spec (.of k))) (L : (pullback f T.hom).Pic),
        L ∈ (picardFunctorNormalized f P hP).obj (op T) →
        L ∈ (picardSubfunctorDegree f 0).obj (op T) →
        ∃! a : T ⟶ J, Scheme.Pic.map (baseChangeMap f a) M = L) ∧
      ∃ (N : C.Pic),
        Nonempty ((fromSkeleton C.Modules).obj N.val ≅ P.ker.toModules) ∧
        (∃ fP : Over.mk f ⟶ J, IsClosedImmersion fP.left ∧
          ∀ (T : Over (Spec (.of k))) (Q : T ⟶ Over.mk f),
            ∃ (LQ : (pullback f T.hom).Pic),
              Nonempty ((fromSkeleton _).obj LQ.val ≅
                (pullback.lift Q.left (𝟙 T.left) Q.w).ker.toModulesᵛ) ∧
              ∃ hQ : LQ * Scheme.Pic.map (pullback.fst f T.hom) N ∈
                  (picardSubfunctorDegree f 0).obj (op T),
                eJ.homEquiv (Q ≫ fP) =
                  (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
                    (picardSubfunctorDegree f 0).toFunctor).app (op T)
                      ⟨LQ * Scheme.Pic.map (pullback.fst f T.hom) N, hQ⟩) ∧
        ∀ r : ℕ, r ≤ g →
          ∃ (H : Over (Spec (.of k))) (eH : (hilbertPresheaf f r).RepresentableBy H)
            (a : H ⟶ J)
            (τ : (picardFunctorDegree f (r : ℤ)).obj ≅ (picardFunctorDegree f 0).obj),
            (∀ (T : Over (Spec (.of k)))
              (L : (picardSubfunctorDegree f (r : ℤ)).toFunctor.obj (op T)),
              ∃ hL : (@id (pullback f T.hom).Pic L.val) *
                  Scheme.Pic.map (pullback.fst f T.hom) (N ^ r) ∈
                  (picardSubfunctorDegree f 0).obj (op T),
                τ.hom.app (op T)
                    ((toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
                      (picardSubfunctorDegree f (r : ℤ)).toFunctor).app (op T) L) =
                  (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
                    (picardSubfunctorDegree f 0).toFunctor).app (op T)
                      ⟨(@id (pullback f T.hom).Pic L.val) *
                        Scheme.Pic.map (pullback.fst f T.hom) (N ^ r), hL⟩) ∧
            (∀ (T : Over (Spec (.of k))) (u : T ⟶ H),
              ∃ (L : (pullback f T.hom).Pic)
                (hL : L ∈ (picardSubfunctorDegree f (r : ℤ)).obj (op T)),
                Nonempty ((fromSkeleton _).obj L.val ≅ (eH.homEquiv u).val.toModulesᵛ) ∧
                eJ.homEquiv (u ≫ a) = τ.hom.app (op T)
                  ((toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
                    (picardSubfunctorDegree f (r : ℤ)).toFunctor).app (op T) ⟨L, hL⟩)) ∧
            IsIntegral a.left.image ∧
            topologicalKrullDim a.left.image = (r : WithBot ℕ∞) ∧
            (∃ b : H.left.PartialIso a.left.image,
              b.iso.hom ≫ b.target.ι = b.source.ι ≫ a.left.toImage) ∧
            (r = g → IsIso a.left.imageι) ∧
            (r = g - 1 → a.left.ker.IsInvertible) := by
  sorry

end AlgebraicGeometry
