module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring

/-! # Relative adjoint character weights on dual-number points

Source: Conrad, Reductive group schemes, Section 4 opening, p.107, and
Proposition 5.2.3, pp.152--153.
(blueprint: def-sfb-relative-adjoint-weights)

The weight equation is tested on every algebra, including nonreduced algebras.
Thus it is the equation for the full torus coaction. Transport in the dual numbers
is characterized by its values on constants and epsilon, which determine it uniquely.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.RelativeAdjointWeights

/-- Evaluation of the Laurent coordinate of an actual multiplicative-group character.
Source: Conrad, Appendix B.1, p.280 (blueprint: def-sfb-relative-adjoint-weights). -/
def characterValue {A : Type u} [CommRing A]
    {T : Grp (Over (Spec (.of A)))}
    (χ : T ⟶ RingGroupSchemes.multiplicative A)
    {C : Type u} [CommRing C] [Algebra A C] (s : points T.X C) : C :=
  (Scheme.ΓSpecIso (.of C)).hom
    ((s ≫ χ.hom.hom).left.appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial A))).inv (LaurentPolynomial.T 1)))

/-- Occurrence of a character in Lie(G) after extension to B. A nonidentity tangent
point at the identity is a nonzero vector. Its conjugate by every torus C-point
is its scalar multiple by the character value, for every B-algebra C. The scalar
multiple is the actual substitution epsilon ↦ chi(s) epsilon. Quantifying over
these test algebras is equivalent to the full coaction eigenvector equation;
no test only on the points of the base ring is used.
Source: Conrad, Section 4, p.107; Proposition 5.2.3, pp.152--153.
(blueprint: def-sfb-relative-adjoint-weights). -/
def HasWeightOver {A : Type u} [CommRing A]
    {T G : Grp (Over (Spec (.of A)))} (i : T ⟶ G)
    (χ : T ⟶ RingGroupSchemes.multiplicative A)
    (B : Type u) [CommRing B] [Algebra A B] : Prop :=
  ∃ v : points G.X (DualNumber B),
    points.map G.X (TrivSqZeroExt.fstHom A B B) v = 1 ∧ v ≠ 1 ∧
    ∀ (C : Type u) [CommRing C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      (φ : DualNumber B →ₐ[A] DualNumber C),
      (∀ b : B, φ (algebraMap B (DualNumber B) b) =
        algebraMap C (DualNumber C) (algebraMap B C b)) →
      φ DualNumber.eps = DualNumber.eps → ∀ s : points T.X C,
      (points.map T.X (TrivSqZeroExt.inlAlgHom A C C) s ≫ i.hom.hom) *
          points.map G.X φ v *
          (points.map T.X (TrivSqZeroExt.inlAlgHom A C C) s ≫ i.hom.hom)⁻¹ =
        points.map G.X ((DualNumber.scale (characterValue χ s)).restrictScalars A)
          (points.map G.X φ v)

/-- The nonzero adjoint weights, as actual characters rather than their differentials.
Source: Conrad, Definition 5.1.1, p.136 (blueprint: def-sfb-relative-adjoint-weights). -/
def rootsOver {A : Type u} [CommRing A]
    {T G : Grp (Over (Spec (.of A)))} (i : T ⟶ G)
    (B : Type u) [CommRing B] [Algebra A B] :
    Set (T ⟶ RingGroupSchemes.multiplicative A) :=
  {χ | χ.hom.hom ≠ 1 ∧ HasWeightOver i χ B}

end AlgebraicGeometry.RelativeAdjointWeights
