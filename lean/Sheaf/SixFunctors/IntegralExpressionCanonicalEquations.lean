/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.SixFunctors.IntegralExpressionTransposeIsIso

/-! # Equations for the canonical expression comparison -/

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

/-- The inverse transposed coefficient comparison has the displayed tree equations.
This is a statement about an already explicitly constructed family; it does not
construct another comparison and asserts no direct compactification agreement.
Source: fix-prop-coherence.proof.md, coefficient-comparison sentence; extracted
expression-recursion proof, steps 2--7
(blueprint: lem-sf-integral-expression-canonical-equations).

Proof: induct on the finite expression, including both tensor children. At a leaf
coefficientMap is identity, so its transpose is the actual unit and its inverse is
the inverse unit. For a unary node let M be the child system. The child comparison
is an isomorphism to its integral value. Reconstruction.limit, reduction, and
counit, together with the Good assumptions at child and parent, give the witness
for basicUnaryDomain at L M. The map L A(e_M) is invertible, so unaryA is an
isomorphism. Take the inverse of the composite unaryA followed by A_int of the
child comparison. Reduce this inverse and compose with the parent counit.
Naturality of r_A and the child coefficient identity move the child inverse past
r_A. Counit naturality at A(e_M), followed by unaryTranspose, identifies the result
with the parent's coefficientMap. Injectivity of the adjunction hom-set equivalence
then identifies this inverse with the explicit transpose. Invert again to get the
claimed equation and include the child induction hypothesis. For tensor use the
same calculation with the pair of child inverses and the tensor of both counits;
tensorTranspose replaces unaryTranspose. Bifunctoriality combines the two induction
hypotheses, with no distinct-variable assumption. For compact support perform the
open step followed by the proper step, retaining the intermediate Good condition
and the finite-type compactification scheme. These are precisely the two domain
witnesses and the composite written in Equations. -/
theorem canonicalComparisons_equations (D : FiniteFieldDatum.{u})
    (o : Operations l E) (d : Primitives l E D o) (rec : Reconstruction l E D)
    {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
    {W : Over (Spec (.of D.k))} (e : Expression _ I X W) (g : e.geometric)
    (K : (e.domain l E o).FullSubcategory) :
    Equations l E d (canonicalComparisons l E D o d rec) e g K := by sorry

end WeilConjectures.IntegralSystemRealization.ExpressionRecursion
