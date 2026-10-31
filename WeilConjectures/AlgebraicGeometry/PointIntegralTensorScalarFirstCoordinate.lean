/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointFibreDerivedTensorCompatibility

/-! Finite coordinate normalization for the point scalar square.

Source: Stacks 07A4 and 0941.
(blueprint: new-lem-sf-point-integral-tensor-scalar-first-coordinate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

/-- The left side of the point scalar square: the `L`-completion of the tensor of the
scalar-extended sections `a • x` and `b • y`.
Source: Stacks 07A4 (blueprint: new-lem-sf-point-integral-tensor-scalar-first-coordinate). -/
def pointIntegralTensorScalarLeft
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (I₁ : PointIntegralTensorData D l hl E) (I₂ : PointIntegralTensorData D l hl L)
    (_C₁ : PointIntegralTensorCanonical D l hl E I₁)
    (_C₂ : PointIntegralTensorCanonical D l hl L I₂)
    (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (p q : ℤ)
    (a b : (completedIntegralCommRingSheafUnrestricted l L
      (Spec (.of D.k))).obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    (x : (P.obj.X p).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    (y : (Q.obj.X q).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))) :=
  ((_C₂.completion
      ⟨_, scalarGood l E L ι (Spec (.of D.k)) P⟩
      ⟨_, scalarGood l E L ι (Spec (.of D.k)) Q⟩).f (p + q))
    ((HomologicalComplex.ιTensorObj
      ((pointIntegralComplexSections D l L).obj
        (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P.obj))
      ((pointIntegralComplexSections D l L).obj
        (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Q.obj)) p q (p + q) rfl).hom
      (integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) (P.obj.X p)
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) a x ⊗ₜ[
          ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l L)]
        integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) (Q.obj.X q)
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) b y))

/-- The right side of the point scalar square: `scalarTensorChain` applied to the scalar
extension by `a * b` of the `E`-completion of `x ⊗ y`.
Source: Stacks 07A4 (blueprint: new-lem-sf-point-integral-tensor-scalar-first-coordinate). -/
def pointIntegralTensorScalarRight
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (I₁ : PointIntegralTensorData D l hl E) (I₂ : PointIntegralTensorData D l hl L)
    (_C₁ : PointIntegralTensorCanonical D l hl E I₁)
    (_C₂ : PointIntegralTensorCanonical D l hl L I₂)
    (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (p q : ℤ)
    (a b : (completedIntegralCommRingSheafUnrestricted l L
      (Spec (.of D.k))).obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    (x : (P.obj.X p).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    (y : (Q.obj.X q).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))) :=
  ((scalarTensorChain l E L ι (Spec (.of D.k)) P.obj Q.obj).f (p + q)).val.app
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))
    (integralOrdinaryTensorSection l E L ι (Spec (.of D.k))
      (((integralOperationsTensorComplexFunctor l E (Spec (.of D.k))).obj
        (P.obj, Q.obj)).X (p + q))
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) (a * b)
      ((_C₁.completion P Q).f (p + q)
        ((HomologicalComplex.ιTensorObj
          ((pointIntegralComplexSections D l E).obj P.obj)
          ((pointIntegralComplexSections D l E).obj Q.obj) p q (p + q) rfl).hom
          (x ⊗ₜ[ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)] y))))

/-- Finite first-coordinate normalization for the scalar square.

Source: Stacks 07A4 and 0941.
Proof: the first mapping-cocone coordinate lands in the product of the finite
tensor levels, and point sections preserve this product, so it suffices to compare
the n-th projections for every n. On the left, C₂.first identifies the n-th
coordinate of the completion of `a•x ⊗ b•y` with the level-n tensor of the
reductions of `a•x` and `b•y`. On the right, scalarTensorChain is the diagonal
Roos map of scalarTensorTower, so its first coordinate followed by the n-th
projection is scalarTensorLevel at level n (scalarTensorTower normalization)
applied to the n-th projection, and C₁.first identifies that projection of the
E-completion of `x ⊗ y` with the level-n tensor of the reductions of `x` and `y`.
The defining equation of scalarTensorLevel sends the scalar extension by `a*b` of
that tensor generator to the tensor of the extended entries, and tensor balance
moves `a` and `b` onto the two factors, which is the left side.
(blueprint: new-lem-sf-point-integral-tensor-scalar-first-coordinate). -/
theorem pointIntegralTensorScalarFirstCoordinate
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (I₁ : PointIntegralTensorData D l hl E) (I₂ : PointIntegralTensorData D l hl L)
    (C₁ : PointIntegralTensorCanonical D l hl E I₁)
    (C₂ : PointIntegralTensorCanonical D l hl L I₂)
    (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (p q : ℤ)
    (a b : (completedIntegralCommRingSheafUnrestricted l L
      (Spec (.of D.k))).obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    (x : (P.obj.X p).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    (y : (Q.obj.X q).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    ((pointIntegralSections l L D.k).map
      ((CochainComplex.mappingCocone.fst
        (pointTensorRoosEndomorphism D l L
          (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P.obj)
          (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q.obj))).f (p + q)))
      (pointIntegralTensorScalarLeft D l hl E L ι I₁ I₂ C₁ C₂ P Q p q a b x y) =
    ((pointIntegralSections l L D.k).map
      ((CochainComplex.mappingCocone.fst
        (pointTensorRoosEndomorphism D l L
          (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P.obj)
          (((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q.obj))).f (p + q)))
      (pointIntegralTensorScalarRight D l hl E L ι I₁ I₂ C₁ C₂ P Q p q a b x y) := by
  sorry

end WeilConjectures
