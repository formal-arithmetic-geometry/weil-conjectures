/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointFibreDerivedTensorCompatibility
import WeilConjectures.AlgebraicGeometry.PointIntegralTensorScalarSecondCoordinate

/-! # Scalar compatibility of the integral point tensor augmentation

Source: Stacks 07A4, 0941 and 031B.
(blueprint: lem-sf-point-integral-tensor-scalar-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

private theorem mappingCocone_element_ext
    {A : Type*} [Category A] [Preadditive A]
    {R : Type u} [Ring R] (F : A ⥤ ModuleCat R) [F.Additive]
    {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    [HomologicalComplex.HasHomotopyCofiber φ]
    {i : ℤ} {x y : F.obj ((CochainComplex.mappingCocone φ).X i)}
    (hfst : F.map ((CochainComplex.mappingCocone.fst φ).f i) x =
      F.map ((CochainComplex.mappingCocone.fst φ).f i) y)
    (hsnd : F.map ((CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega)) x =
      F.map ((CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega)) y) : x = y := by
  have he := congrArg (fun f => F.map f)
    (CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega))
  have hex := congrArg (fun f => f.hom) he
  have hx := congrArg (fun f => f x) hex
  have hy := congrArg (fun f => f y) hex
  have hx' : x =
      (ModuleCat.Hom.hom (F.map ((CochainComplex.mappingCocone.inl φ).v i i (by omega))))
          ((ModuleCat.Hom.hom (F.map ((CochainComplex.mappingCocone.fst φ).f i))) x) +
        (ModuleCat.Hom.hom (F.map ((CochainComplex.mappingCocone.inr φ).1.v
          (i - 1) i (by omega))))
          ((ModuleCat.Hom.hom (F.map ((CochainComplex.mappingCocone.snd φ).v i (i - 1)
            (by omega)))) x) := by
    simpa using hx.symm
  have hy' :
      (ModuleCat.Hom.hom (F.map ((CochainComplex.mappingCocone.inl φ).v i i (by omega))))
          ((ModuleCat.Hom.hom (F.map ((CochainComplex.mappingCocone.fst φ).f i))) y) +
        (ModuleCat.Hom.hom (F.map ((CochainComplex.mappingCocone.inr φ).1.v
          (i - 1) i (by omega))))
          ((ModuleCat.Hom.hom (F.map ((CochainComplex.mappingCocone.snd φ).v i (i - 1)
            (by omega)))) y) = y := by
    simpa using hy
  rw [hx', hfst, hsnd]
  exact hy'

set_option maxHeartbeats 800000 in
-- The coordinate extensionality reduction needs a larger elaboration budget.
/-- Normalized completion maps commute with the specified scalar tensor chain.
Source: Stacks 07A4 and 0941, integral point comparison proof step 2
(blueprint: lem-sf-point-integral-tensor-scalar-compatibility).

Proof: the target of both displayed sections is the point sections of a mapping
cocone. By the additive identity `inl ∘ fst + inr ∘ snd = 𝟙` of the mapping
cocone (`mappingCocone_element_ext`), two elements agree once their first
(product) coordinates and their shifted coordinates agree after the additive
section functor. The first coordinates agree by the finite quotient
normalization pointIntegralTensorScalarFirstCoordinate; the shifted coordinates
agree by pointIntegralTensorScalarSecondCoordinate (both are zero). This is an
identity of actual chain representatives, independent of the derived monoidal data. -/
theorem pointIntegralTensorScalarCompatibility
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (I₁ : PointIntegralTensorData D l hl E) (I₂ : PointIntegralTensorData D l hl L)
    (C₁ : PointIntegralTensorCanonical D l hl E I₁)
    (C₂ : PointIntegralTensorCanonical D l hl L I₂) :
    PointIntegralTensorScalarSquare D l hl E L ι I₁ I₂ C₁ C₂ := by
  intro P Q p q a b x y
  let P' : (integralOperationsGoodComplex l L (Spec (.of D.k))).FullSubcategory :=
    ⟨((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P.obj, scalarGood l E L ι (Spec (.of D.k)) P⟩
  let Q' : (integralOperationsGoodComplex l L (Spec (.of D.k))).FullSubcategory :=
    ⟨((integralOrdinaryScalar l E L ι (Spec (.of D.k))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Q.obj, scalarGood l E L ι (Spec (.of D.k)) Q⟩
  have hfirst := pointIntegralTensorScalarFirstCoordinate D l hl E L ι I₁ I₂ C₁ C₂
    P Q p q a b x y
  have hsecond := pointIntegralTensorScalarSecondCoordinate D l hl E L ι I₁ I₂ C₁ C₂
    P Q p q a b x y
  let F := pointIntegralSections l L D.k
  let φ := pointTensorRoosEndomorphism D l L P'.obj Q'.obj
  apply mappingCocone_element_ext F φ
  · simpa [F, φ, P', Q', pointIntegralTensorScalarLeft,
      pointIntegralTensorScalarRight] using hfirst
  · simpa [F, φ, P', Q', pointIntegralTensorScalarLeft,
      pointIntegralTensorScalarRight] using hsecond

end WeilConjectures
