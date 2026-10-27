/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.SixFunctors.IntegralExpressionRecursionData

/-! # Invertibility of the expression coefficient transpose -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField
  WeilConjectures.integralDerivedPullback WeilConjectures.integralCompletedTensor
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization.ExpressionRecursion
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The explicitly transposed coefficient map is invertible on the expression domain.
No recursive equations or compactification normalization are asserted here.
Source: fix-prop-coherence.proof.md, coefficient-comparison sentence; the extracted
expression-recursion proof, steps 1--7
(blueprint: lem-sf-integral-expression-transpose-is-iso).

Proof: induct on the finite expression. At a leaf the transpose is the actual unit,
which Reconstruction.unit makes invertible. For a unary node, let M be the child
system and H its integral value. The induction hypothesis identifies H with L M.
Reconstruction.limit and the child Good condition show L M is constructible;
Reconstruction.reduction gives Good (R L M), and Reconstruction.counit identifies
R L M with M. Transport Good along this isomorphism, and through the unary
functor, to obtain the required basicUnaryDomain witness at L M. The given d_A
and inverse of L A(e_M) are isomorphisms there. Naturality of r_A at the child
transpose and the assumed primitive transpose identity show the parent transpose
is A_int of the child transpose followed by the inverse of a_A(M): apply the
adjunction hom-set equivalence, use counit naturality at A(e_M), and cancel the
child transpose. This is a composite of isomorphisms. For tensor do the same with
the pair of child transposes and counits; the tensor functor preserves that pair
of isomorphisms. For compact support apply the unary argument first to the open
extension and then to proper image. The expression domain retains the intermediate
open Good condition and the geometric hypotheses make its compactification scheme
finite type. No invertibility on objects outside the stated domains is needed. -/
theorem transposeComparison_isIso (D : FiniteFieldDatum.{u})
    (o : Operations l E) (d : Primitives l E D o) (rec : Reconstruction l E D)
    {I : Type u} {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (g : e.geometric)
    (K : (e.domain l E o).FullSubcategory) :
    IsIso ((transposeComparison l E d e g).app K) := by sorry

/-- The comparison is the inverse of the explicit adjunction transpose.
The preceding theorem supplies only its invertibility, hence determines its
inverse uniquely; no arbitrary object is selected from an existence statement.
Source: fix-prop-coherence, expression counit substitution
(blueprint: lem-sf-integral-expression-transpose-is-iso). -/
def canonicalComparisons (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (d : Primitives l E D o) (rec : Reconstruction l E D) : Comparisons l E D o := by
  intro I _ X W e g
  let t := transposeComparison l E d e g
  haveI : ∀ K, IsIso (t.app K) := fun K ↦ transposeComparison_isIso l E D o d rec e g K
  haveI : IsIso t := NatIso.isIso_of_isIso_app t
  exact (asIso t).symm

/-- The canonical comparison satisfies the prescribed whole-system coefficient identity.
Proof: its inverse is the explicit transpose, and the inverse adjunction hom-set
equivalence sends that transpose back to the coefficient map.
Source: fix-prop-coherence, counit substitution
(blueprint: lem-sf-integral-expression-transpose-is-iso). -/
theorem canonicalComparisons_coefficient (D : FiniteFieldDatum.{u})
    (o : Operations l E) (d : Primitives l E D o) (rec : Reconstruction l E D)
    {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (g : e.geometric)
    (K : (e.domain l E o).FullSubcategory) :
    coefficientMap l E d e g K.obj =
      (calculus l E W.left).reduction.map
        ((canonicalComparisons l E D o d rec e g).inv.app K) ≫
      (calculus l E W.left).adjunction.counit.app
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) := by
  exact (transposeComparison_coefficient l E d e g K).symm

end WeilConjectures.IntegralSystemRealization.ExpressionRecursion
