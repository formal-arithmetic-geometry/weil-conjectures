/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.CompletedPullbackTowerRealizations

/-! # Associativity for coherent pullback tensor representatives

Source: Stacks 07A4, `lemma-pullback-tensor-product`, and 07A2,
`lemma-tensor-product-K-flat`.
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] pullbackTensorCalculus pullbackTensorSequenceDerived
  pullbackTensorSystemComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Associativity on three localized coherent K-flat representatives.
Source: Stacks 07A4, total tensor construction; 07A2, K-flat tensor products.
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives).
Proof: total tensors of K-flat complexes are K-flat: reassociate an acyclic
test tensor and apply the two K-flat criteria. Apply the normalization of the
coherent comparison to (A,B), (B,C), (A tensor B,C) and (A,B tensor C), and
use preservation of K-flatness by the sequence inverse image. In every triple
degree both ordinary paths send the adjunction-unit image of (x tensor y)
tensor z to the tensor of the unit images of x, y and z, with parentheses on
the right. Naturality of the unit and the two normalized pure-tensor formulas
identify these sections. Reassociation introduces no permutation or extra sign
and commutes with all three signed differential terms. Tensor sheafification
and the total coproduct injections detect equality, so the chain maps agree.
Apply the derived quotient and insert the fixed tensor-model and exact-pullback
factorization isomorphisms. Their naturality cancels the intermediate maps;
the model associators identify the remaining reassociation maps with the
specified derived associators. This proves the equation on the displayed
representatives; extension to arbitrary derived objects is a separate step. -/
-- STATEMENT-DISPUTED: The selected system calculus does not record compatibility of its
-- monoidal associator with its K-flat tensor comparison. CoefficientTensorModels fixes
-- comparison and closed uncurrying only; neither field mentions the associator. The
-- proof's final identification therefore needs an additional normalization or a repair
-- of the selected calculus. RingedDerivedTensorCoherence.associator_model records the
-- needed compatibility, but its existence theorem chooses a different closed structure
-- and tensor model; it does not apply to the arbitrary calculus chosen here.
-- The missing equation is the associator-model square for the *selected* pair
-- `(pullbackTensorCalculus l E W).systemClosed` and
-- `(pullbackTensorCalculus l E W).systemTensorModel`; no declaration in the imported
-- interface supplies that square. In general, transporting a monoidal structure by
-- an arbitrary binary tensorator preserves its pairwise comparison and uncurrying
-- formulas while changing the associator by a coboundary, so those formulas cannot
-- imply this equation. The representative theorem is therefore retained as a
-- disputed obligation until that interface is repaired.
theorem completedPullbackTensor_associativity_representatives {X Y : Scheme.{u}}
    (f : X ⟶ Y) (A B C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) A)
    (hB : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) B)
    (hC : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) C) :
    let M := DerivedCategory.Q.obj A
    let N := DerivedCategory.Q.obj B
    let P := DerivedCategory.Q.obj C
    (pullbackTensorSequenceDerived l E f).map
      ((pullbackTensorCalculus l E Y).systemClosed.monoidal.associator M N P).hom ≫
      (pullbackTensorSystemComparison l E f).hom.app
        (M,(pullbackTensorCalculus l E Y).systemClosed.tensor.obj (N,P)) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom (𝟙 _) ((pullbackTensorSystemComparison l E f).hom.app (N,P))) =
    (pullbackTensorSystemComparison l E f).hom.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M,N),P) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom ((pullbackTensorSystemComparison l E f).hom.app (M,N)) (𝟙 _)) ≫
      ((pullbackTensorCalculus l E X).systemClosed.monoidal.associator
        ((pullbackTensorSequenceDerived l E f).obj M)
        ((pullbackTensorSequenceDerived l E f).obj N)
        ((pullbackTensorSequenceDerived l E f).obj P)).hom := by sorry

end WeilConjectures
