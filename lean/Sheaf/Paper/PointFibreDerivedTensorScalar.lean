/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointFibreDerivedTensorBasic
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Canonical point tensor comparison interfaces

Source: Stacks 07A4 and the recorded coefficient constructions.
(blueprint: def-sf-point-fibre-tensor-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v c e d hc he hd w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

/-- Ordinary-module derived coefficient extension, using the recorded universal
fixed-second-factor construction with the new coefficient ring in degree zero.
Source: Stacks 06Y6 (blueprint: def-sf-point-fibre-tensor-reduction). -/
@[no_expose] def pointModuleDerivedExtension {R S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : DerivedCategory (ModuleCat.{v} R) ⥤
      DerivedCategory (ModuleCat.{v} S) :=
  (Classical.choose (DerivedCategory.exists_derivedTensor_second_factor_functor f).2).obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (ModuleCat.of S S))

/-- Ordinary module scalar extension has its specified adjunction in this carrier size.
Source: the tensor/restriction adjunction
(blueprint: def-sf-point-fibre-tensor-reduction). -/
noncomputable instance pointModuleScalarLeftAdjoint
    {R S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{v, v, v} f).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{v, v, v} f).isLeftAdjoint

/-- A canonical strong scalar-extension tensorator. The universal derived counit is
retained; the tensorator is fixed by the balanced rule a tensor (x tensor y) maps to
(a tensor x) tensor (1 tensor y). This is also the target reduction comparison.
Source: Stacks 06YS, 06Y6 and 07A4
(blueprint: def-sf-point-fibre-tensor-reduction). -/
structure PointModuleScalarTensorData {R S : Type v} [CommRing R] [CommRing S]
    [HasDerivedCategory.{v} (ModuleCat.{v} R)]
    [HasDerivedCategory.{v} (ModuleCat.{v} S)]
    (f : R →+* S) (H : DerivedCategory (ModuleCat.{v} R) ⥤
      DerivedCategory (ModuleCat.{v} S)) where
  /-- The universal derived comparison to ordinary termwise tensor. -/
  counit : DerivedCategory.Q ⋙ H ⟶
    (ModuleCat.extendScalars.{v, v, v} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q
  /-- The actual universal property, including all unbounded inputs. -/
  universal : H.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ))
  /-- Strong scalar extension with its associator and unitor diagrams. -/
  strong : H.Monoidal
  /-- The tensor comparison is the canonical balanced map on representatives. -/
  tensor_model : ∀ P Q : CochainComplex (ModuleCat.{v} R) ℤ,
    ∃ e : ((ModuleCat.extendScalars.{v, v, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (P ⊗ Q) ≅
        ((ModuleCat.extendScalars.{v, v, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⊗
          ((ModuleCat.extendScalars.{v, v, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q,
      (∀ (p q k : ℤ) (h : p + q = k) (a : S) (x : P.X p) (y : Q.X q),
        (e.hom.f k) (a ⊗ₜ[R, f] ((HomologicalComplex.ιTensorObj P Q p q k h)
          (x ⊗ₜ[R] y))) =
        (HomologicalComplex.ιTensorObj
          (((ModuleCat.extendScalars.{v, v, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (((ModuleCat.extendScalars.{v, v, v} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
          p q k h) ((a ⊗ₜ[R, f] x) ⊗ₜ[S] ((1 : S) ⊗ₜ[R, f] y))) ∧
      H.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫ counit.app (P ⊗ Q) ≫
          DerivedCategory.Q.map e.hom =
        (@Functor.OplaxMonoidal.δ _ _ _ _ _ _ H strong.toOplaxMonoidal
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)) ≫
        (MonoidalCategory.tensor _).map (Prod.mkHom (counit.app P) (counit.app Q)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q _ _

/-- The finite quotient on ordinary coefficient rings, with only the recorded ULift.
Source: normalized quotient coefficient construction
(blueprint: def-sf-point-fibre-tensor-reduction). -/
def pointFiniteCoefficientQuotient
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {m n : ℕ} (h : n ≤ m) :
    ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)) →+*
      ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)) :=
  RingHom.ulift (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.succ_le_succ h) :
      Padic.coefficientExtensionIdeal l E (m + 1) ≤ Padic.coefficientExtensionIdeal l E (n + 1)))

/-- The recorded quotient tensor comparison with explicitly named finite tensor endpoints.
Its closed transpose is finiteIntrinsicReductionHom.
Source: coefficient evaluation calculus (blueprint: def-sf-point-fibre-tensor-reduction). -/
@[no_expose] def pointFiniteReductionTensor
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {m n : ℕ} (h : n ≤ m) :
    finiteIntrinsicDerivedTensor l E (Spec (.of D.k)) m ⋙
        coefficientFiniteQuotientDerived l E (Spec (.of D.k)) h ≅
      (coefficientFiniteQuotientDerived l E (Spec (.of D.k)) h).prod
        (coefficientFiniteQuotientDerived l E (Spec (.of D.k)) h) ⋙
          finiteIntrinsicDerivedTensor l E (Spec (.of D.k)) n :=
  (coefficientDerivedSystemEvaluationCalculus l E
    (Spec (.of D.k))).choose.quotientCalculus.tensor h

/-- A finite reduction square using the exact quotient tensor comparison whose closed
transpose is `finiteIntrinsicReductionHom`. The fibre comparison is pinned on every
K-flat quotient model by 1 tensor x; the final equality is the actual cross-level
square, involving the tensorators at m and n and derived scalar extension.
Source: node proof step 9; Stacks 07A4
(blueprint: def-sf-point-fibre-tensor-reduction). -/
def PointFiniteTensorReductionData
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {m n : ℕ} (h : n ≤ m) (Sₘ : PointFiniteTensorData D l E m)
    (Sₙ : PointFiniteTensorData D l E n) : Prop :=
  /- The canonical target derived quotient tensor. -/
  ∃ target : PointModuleScalarTensorData (pointFiniteCoefficientQuotient l E h)
    (pointModuleDerivedExtension (pointFiniteCoefficientQuotient l E h)),
  /- Evaluation commutes with the specified derived quotient. -/
  ∃ fibre : coefficientFiniteQuotientDerived l E (Spec (.of D.k)) h ⋙
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory ≅
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory ⋙
        pointModuleDerivedExtension (pointFiniteCoefficientQuotient l E h),
  /- Canonical normalization on representatives. -/
  (∀ (P : CochainComplex (normalizedDVRModules l E (Spec (.of D.k)) m) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (Scheme.ProEt (Spec (.of D.k))) inferInstance (essentiallySmallSelf.{0} _)
      (Scheme.ProEt.topology (Spec (.of D.k)))
      (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) m) P),
    ∃ e : (pointFiniteComplexSections D l E n).obj
        (((coefficientFiniteQuotientExtension l E (Spec (.of D.k)) h).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≅
      ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointFiniteCoefficientQuotient l E h)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((pointFiniteComplexSections D l E m).obj P),
      (∀ (k : ℤ) (x : (P.X k).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))),
        (e.hom.f k) (coefficientFiniteQuotientUnitSection l E (Spec (.of D.k)) h
          (P.X k) (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) x) =
          (1 : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) ⊗ₜ[
            ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)),
            pointFiniteCoefficientQuotient l E h]
            (@id ((pointFiniteSections D.k
              (Padic.coefficientExtensionRing l E (m + 1))).obj (P.X k)) x)) ∧
      fibre.hom.app (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P) ≫
        (pointModuleDerivedExtension (pointFiniteCoefficientQuotient l E h)).map
          ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E
            (m + 1))).mapDerivedCategoryFactors.{u + 2, u + 1}.hom.app P) ≫
        target.counit.app ((pointFiniteComplexSections D l E m).obj P) =
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E
        (n + 1))).mapDerivedCategory.{u + 2, u + 1}.map
          (coefficientFiniteQuotientModel l E (Spec (.of D.k)) h P hP).hom ≫
        (pointFiniteSections D.k (Padic.coefficientExtensionRing l E
          (n + 1))).mapDerivedCategoryFactors.{u + 2, u + 1}.hom.app _ ≫
          DerivedCategory.Q.map e.hom) ∧
  /- The reduction square includes every identity quotient. -/
  ∀ (M N : finiteTorConstructibleCategory l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) (Spec (.of D.k))),
    ∃ (hM : finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
        (Spec (.of D.k)) ((coefficientFiniteQuotientDerived l E (Spec (.of D.k)) h).obj M.obj))
      (hN : finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
        (Spec (.of D.k)) ((coefficientFiniteQuotientDerived l E (Spec (.of D.k)) h).obj N.obj)),
      HEq
      ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E
        (n + 1))).mapDerivedCategory.{u + 2, u + 1}.map
          ((pointFiniteReductionTensor D l E h).hom.app (M.obj, N.obj)) ≫
        (Sₙ.tensorIso ⟨_, hM⟩ ⟨_, hN⟩).hom ≫
        (MonoidalCategory.tensor _).map
          (Prod.mkHom (fibre.hom.app M.obj) (fibre.hom.app N.obj)))
      (fibre.hom.app ((finiteIntrinsicDerivedTensor l E (Spec (.of D.k)) m).obj
        (M.obj, N.obj)) ≫
        (pointModuleDerivedExtension (pointFiniteCoefficientQuotient l E h)).map
          (Sₘ.tensorIso M N).hom ≫
        (@Functor.OplaxMonoidal.δ _ _ _ _ _ _ _ target.strong.toOplaxMonoidal
          ((finitePointFibreTensorSource D l E m).obj M)
          ((finitePointFibreTensorSource D l E m).obj N)))


end WeilConjectures
