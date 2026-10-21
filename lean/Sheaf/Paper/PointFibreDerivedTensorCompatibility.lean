/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointFibreDerivedTensorModels
public import Sheaf.Paper.PointFibreDerivedTensorFiniteModels
/-! # Finite source constraints and integral scalar tensor squares

Source: Stacks 07A4 and the recorded coefficient constructions.
(blueprint: def-sf-point-finite-source-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

/-- The source constraints at finite level are the restrictions of the recorded
closed derived tensor, not newly selected associators or unitors.
Source: finiteIntrinsicClosed (blueprint: def-sf-point-finite-source-constraints). -/
def PointFiniteSourceConstraints
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (S : PointFiniteTensorData D l E n) : Prop :=
  letI := (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal
  ∃ J : @Functor.Monoidal _ _ S.monoidal _ _
      (finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal
      (finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
        (Spec (.of D.k))).ι,
    (∀ X Y, HEq
      (@Functor.LaxMonoidal.μ _ _ S.monoidal _ _ _ _ J.toLaxMonoidal X Y)
      (eqToHom (congrArg (fun G ↦ G.obj (X, Y)) S.tensor_eq).symm)) ∧
    HEq (@Functor.LaxMonoidal.ε _ _ S.monoidal _ _ _ _ J.toLaxMonoidal)
      (eqToHom S.unit_eq.symm)

/-- Compatibility with the actual integral scalar/completed-tensor comparison.
This is the square on good representatives: scalarTensorChain is the specified
map on both Roos coordinates. Together with the completion normalization above,
it fixes the derived scalar square, including identity embeddings.
Source: scalarTensorOrdinary representative equation, Stacks 07A4 and 0941
(blueprint: def-sf-point-integral-scalar-square). -/
def PointIntegralTensorScalarSquare
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (I₁ : PointIntegralTensorData D l hl E) (I₂ : PointIntegralTensorData D l hl L)
    (C₁ : PointIntegralTensorCanonical D l hl E I₁)
    (C₂ : PointIntegralTensorCanonical D l hl L I₂) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (p q : ℤ)
    (a b : (completedIntegralCommRingSheafUnrestricted l L
      (Spec (.of D.k))).obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    (x : (P.obj.X p).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    (y : (Q.obj.X q).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))),
    ((C₂.completion
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
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) b y)) =
    ((scalarTensorChain l E L ι (Spec (.of D.k)) P.obj Q.obj).f (p + q)).val.app
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))
      (integralOrdinaryTensorSection l E L ι (Spec (.of D.k))
        (((integralOperationsTensorComplexFunctor l E (Spec (.of D.k))).obj
          (P.obj, Q.obj)).X (p + q))
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) (a * b)
        (((C₁.completion P Q).f (p + q))
          ((HomologicalComplex.ιTensorObj
            ((pointIntegralComplexSections D l E).obj P.obj)
            ((pointIntegralComplexSections D l E).obj Q.obj) p q (p + q) rfl).hom
            (x ⊗ₜ[ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)] y))))

end WeilConjectures
