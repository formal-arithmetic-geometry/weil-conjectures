module

public import Sheaf.AlgebraicGeometry.PGLLinearizedPolarization
public import Sheaf.AlgebraicGeometry.HilbertPluckerPGLLinearization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.ProjectivePolarizationSectionAlgebra
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.RepresentationTheory.PGLGeometricReductivity
import Sheaf.AlgebraicGeometry.FiniteGradedProjProjective
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Flat.Basic
import Sheaf.AlgebraicGeometry.AffineActionStackPresentation
import Sheaf.AlgebraicGeometry.AdequateModuliUniversalClosedTopology
import Sheaf.AlgebraicGeometry.AffineActionQuotientStack
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Projective PGL quotients and universal closed images

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Algebraic Geometry 1 (2014), pp.490--491, Theorems 9.1.4, 9.7.6, 6.3.3 and
5.3.1(2), with Proposition 5.2.9(3)
(blueprint: lem-sfb-projective-pgl-invariant-quotient).

The recorded PGL action is tested on all schemes, including nonreduced schemes.
For a closed subscheme after base change, invariance means that every translate
of a test point factors through that same closed subscheme over the same base
point. By the functor of points this is preservation of the defining ideal.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.PGLLinearization

/-- The semistable open has an affine, surjective finite-type invariant quotient
with projective finite-type target. After every base change, the image of every
scheme-theoretically invariant closed subscheme is closed.
Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
pp.490--491, Theorems 9.1.4, 9.7.6, 6.3.3 and 5.3.1(2), Proposition 5.2.9(3)
(blueprint: lem-sfb-projective-pgl-invariant-quotient).

Proof, following the eight DAG steps:
1. By lem-weil-pbc-ample-very-ample-immersion-affine-base, a power of L comes from
   an immersion into projective space. Projectivity makes Z proper; the target
   is separated by lem-pc-projective-proper. Apply lem-weil-pbc-proper-to-separated
   and lem-weil-pbc-proper-immersion-closed to make the immersion closed. Then
   lem-sfb-projective-polarization-section-algebra identifies the section algebra
   S, proves finite generation and finite-dimensionality of each piece, and
   identifies every positive-degree nonvanishing chart with Spec S_(s).
2. The linearization induces a graded coaction on S, using degree-zero
   lem-sc-flat-base-change-coherent and lem-weil-pbc-module-over-field-flat with
   coefficient algebra k[G]. Its identity, cocycle and tensor laws give the
   coaction laws. By lem-sfb-pgl-geometric-reductivity, R = S^G is finitely
   generated. Since R_0 lies in the finite-dimensional S_0,
   lem-sfb-finite-graded-proj-projective makes Q = Proj R projective finite type;
   R_0 need not equal k.
3. The invariant nonvanishing opens cover exactly the geometric semistable open
   of lem-sfb-hilbert-plucker-pgl-linearization and
   def-sfb-pgl-linearized-polarization. The flat-base-change theorem and
   lem-weil-pbc-flat-tensor-exact identify invariants after algebraically closed
   extension by tensoring the kernel of the coaction minus v maps to v tensor 1.
   A nonzero linear combination at a point has a nonzero summand. Each such open
   is invariant on all test schemes.
4. On Z_s, invariants of S_(s) equal R_(s). For an invariant fraction a/s^n,
   some power of s tensor 1 annihilates its coaction defect, so multiplying its
   numerator and denominator by that power makes the numerator invariant.
   The same localization relation proves injectivity, even with zero divisors.
5. The inclusions R_(s) into S_(s) give invariant chart maps by
   lem-weil-pbc-morphism-into-affine-scheme and def-pc-proj. By
   lem-weil-pbc-proj-basic-open-intersection, their overlap is the locus where
   t^degree(s)/s^degree(t) is invertible. The fraction maps agree there, so
   lem-weil-pbc-scheme-morphism-gluing constructs q with preimage of D_+(s)
   exactly Z_s. The same uniqueness proves invariance.
6. By pqf-lem-affine-local-target, q is affine. Z is Noetherian by
   lem-weil-pbc-finite-type-over-noetherian, so its opens are quasi-compact by
   lem-weil-pbc-noetherian-open-subscheme-noetherian. Over any affine target open,
   principal opens in the Z_s give finite-type coordinate algebras over k and
   hence over the target algebra; a finite subcover proves finite type of q.
7. Use lem-sfb-pgl-reductive-structure and lem-sfb-pgl-geometric-reductivity with
   lem-sfb-power-lifting-adequate-affine-quotient on each chart. The smooth
   surjective atlas of lem-sfb-affine-action-stack-presentation, followed by the
   adequate map, is q_s. Surjectivity from
   lem-sfb-adequate-moduli-universal-closed-topology proves q is surjective.
8. For arbitrary T to Q, restrict to T_s over D_+(s). The base-changed atlas is
   smooth surjective by lem-sfb-stack-chartwise-smooth-etale-calculus. The closed
   subscheme C is saturated for this atlas: equality of quotient-stack points
   means translation after a common field extension, by
   def-sfb-affine-action-quotient-stack; ideal vanishing is reflected by field
   extension and invariance is reflected using the inverse group element.
   Its image in the stack is therefore closed by the atlas topology. The
   universal closedness of lem-sfb-adequate-moduli-universal-closed-topology
   makes its image in T_s closed. These images are precisely the restrictions
   of the image of C, so closedness on this open cover proves the claim.
   No flatness of T to Q or adequacy of the base-changed map is required. -/
theorem projective_pgl_invariant_quotient
    (k : Type u) [Field k] (r : ℕ) (hr : 2 ≤ r)
    (Z : Over (Spec (.of k))) (hprojective : IsHProjective Z.hom)
    (hfiniteType : LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom)
    (L : Z.left.Modules) [L.IsInvertible] (hample : Scheme.Modules.IsAmple Z.left L)
    (D : Action k r Z L) :
    ∃ U : Z.left.Opens,
      (∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
        (x : fieldTest k Ω ⟶ Z),
        x.left.base (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω) ∈ U ↔
          D.IsSemistable Ω x) ∧
      ∃ (Q : Over (Spec (.of k))) (q : Over.mk (U.ι ≫ Z.hom) ⟶ Q),
        IsHProjective Q.hom ∧ LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom ∧
        Surjective q.left ∧ LocallyOfFiniteType q.left ∧ QuasiCompact q.left ∧
        IsAffineHom q.left ∧
        (∀ (W : Over (Spec (.of k))) (g : Matrices k r W)
          (x y : W ⟶ Over.mk (U.ι ≫ Z.hom)),
          y ≫ (Over.homMk U.ι : Over.mk (U.ι ≫ Z.hom) ⟶ Z) =
            D.act W g (x ≫ (Over.homMk U.ι : Over.mk (U.ι ≫ Z.hom) ⟶ Z)) →
            y ≫ q = x ≫ q) ∧
        (∀ (T : Over (Spec (.of k))) (t : T ⟶ Q)
          (C : Over (Spec (.of k))) (i : C ⟶ pullback q t),
          IsClosedImmersion i.left →
          (∀ (W : Over (Spec (.of k))) (g : Matrices k r W) (x : W ⟶ C),
            ∃ y : W ⟶ C,
              y ≫ i ≫ pullback.snd q t = x ≫ i ≫ pullback.snd q t ∧
              y ≫ i ≫ pullback.fst q t ≫
                  (Over.homMk U.ι : Over.mk (U.ι ≫ Z.hom) ⟶ Z) =
                D.act W g (x ≫ i ≫ pullback.fst q t ≫
                  (Over.homMk U.ι : Over.mk (U.ι ≫ Z.hom) ⟶ Z))) →
          IsClosed (Set.range (i ≫ pullback.snd q t).left)) := by
  sorry

end AlgebraicGeometry.PGLLinearization
