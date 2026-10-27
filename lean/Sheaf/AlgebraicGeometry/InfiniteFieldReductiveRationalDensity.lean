module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.Algebra.Field.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Connected.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
import Mathlib.AlgebraicGeometry.Scheme

/-! # Rational points of reductive groups over infinite fields

Source: Milne, Algebraic Groups (2017), Theorem 17.93(b), printed p.382,
including its rational-point density conclusion; Theorem 25.9(a), p.546
(blueprint: lem-sfb-infinite-field-reductive-rational-density).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ReductiveTorusCentralizer

/-- Every nonempty open subscheme of a reductive group over an infinite field has
a rational point, and the images of rational points are Zariski dense.
Source: Milne, Theorem 17.93(b), printed p.382; Theorem 25.9(a), p.546
(blueprint: lem-sfb-infinite-field-reductive-rational-density).

Proof: (1) By lem-sfb-cartan-product-dominance, choose finitely many maximal k-tori
whose centralizers have a dominant multiplication map to G. Reductivity supplies
smoothness, geometric connectedness, affineness and finite type.
(2) By lem-sfb-maximal-torus-field-extension they remain maximal over the algebraic
closure. Apply lem-sfb-reductive-torus-self-centralizer to identify each centralizer
with its torus. Their product P is a torus: after scalar extension, concatenate the
coordinates of the split tori, using def-pc-fibre-product and
def-sfb-tori-multiplicative-type. By lem-sfb-torus-unirational-parametrization,
there is a dominant map q from a nonempty open U of affine n-space to P.
(3) For a nonempty open V of G, dominance of multiplication and of q makes its
inverse image W nonempty. Continuity makes W open in U, hence in affine n-space.
(4) Using def-weil-affine-spectrum, choose a principal open D(f) contained in W
with f nonzero. Regard f as a Laurent polynomial. The
lem-sfb-laurent-vector-evaluation-test with vector space k and subspace zero gives
some tuple of nonzero k-coordinates at which f does not vanish. Evaluation defines
a k-point in D(f). This also works for n = 0, when f is a nonzero constant.
(5) Use lem-weil-pbc-morphism-factors-through-open-subscheme to factor this point
through W, compose with q and multiplication, and factor through V. All maps are
over k; the factorization therefore satisfies the displayed structure-map identity.
Every nonempty open meets the image of a k-point, so the complement of the closure
of all such images must be empty. Conversely density meets each nonempty open,
and open factorization gives a k-point of that open. No perfectness is used. -/
theorem rationalPoints_dense_of_isReductive {k : Type u} [Field k] [Infinite k]
    (G : Grp (Over (Spec (.of k)))) (hG : IsReductive G) :
    (∀ V : G.X.left.Opens, (V : Set G.X.left).Nonempty →
      ∃ p : Spec (.of k) ⟶ V.toScheme,
        p ≫ V.ι ≫ G.X.hom = 𝟙 (Spec (.of k))) ∧
    DenseRange (fun p : Over.mk (𝟙 (Spec (.of k))) ⟶ G.X ↦
      p.left.base (IsLocalRing.closedPoint k)) := by
  sorry

end AlgebraicGeometry.ReductiveTorusCentralizer
