/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointFibreDerivedTensorQbar
public import Sheaf.Paper.PointFibreDerivedTensorModels
public import Sheaf.Paper.PointFibreDerivedTensorFiniteModels
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.GeometricStalkToposPoint
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CoefficientFrobenius
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Paper.PointSectionsDerivedReduction
import Sheaf.Paper.PointSectionsFiniteness
import Sheaf.Paper.PointSectionsScalarExtension
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.RingedTopoiDerivedPullback
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-! # Canonical point tensor comparison interfaces

Source: Stacks 07A4 and the recorded coefficient constructions.
(blueprint: lem-sf-point-fibre-derived-tensor).
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

/-- The source constraints at finite level are the restrictions of the recorded
closed derived tensor, not newly selected associators or unitors.
Source: finiteIntrinsicClosed (blueprint: lem-sf-point-fibre-derived-tensor). -/
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
(blueprint: lem-sf-point-fibre-derived-tensor). -/
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

/-- All canonical normalizations and actual cross-stage diagrams for the simultaneous
strong symmetric monoidal fibre functors. Each scalar functor has its universal
counit and balanced tensorator, rather than an unspecified isomorphism.
Source: node proof steps 2--9 (blueprint: lem-sf-point-fibre-derived-tensor). -/
structure PointFibreDerivedTensorCanonical
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (S : PointFibreDerivedTensorSystem D l hl Ω) where
  /-- Finite source associators and unitors are the recorded ones. -/
  finite_source : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ), PointFiniteSourceConstraints D l E n (S.finite E n)
  /-- Every finite comparison is the canonical map on K-flat models. -/
  finite_model : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ), PointFiniteTensorCanonical D l E n (S.finite E n)
  /-- The full integral two-coordinate Roos normalization. -/
  integral_model : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointIntegralTensorCanonical D l hl E (S.integral E)
  /-- All finite quotient squares, including m = n. -/
  reduction : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (m n : ℕ) (h : n ≤ m),
    PointFiniteTensorReductionData D l E h (S.finite E m) (S.finite E n)
  /-- Integral scalar extension uses the specified scalarTensorChain. -/
  integral_scalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    PointIntegralTensorScalarSquare D l hl E L ι (S.integral E) (S.integral L)
      (integral_model E) (integral_model L)
  /-- The actual coefficient/carrier lift, with its pure-tensor normalization. -/
  lift : ∀ (E : Type u) [Field E], PointFibreLiftTensorData E
  /-- Canonical derived fraction-field tensor. -/
  localization : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointModuleScalarTensorData (pointIntegralToField l E)
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E)).mapDerivedCategory
  /-- Its counit is the recorded exact-functor localization comparison. -/
  localization_counit : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], (localization E).counit =
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategoryFactors.hom
  /-- Rational comparison is precisely the localized integral comparison. -/
  rational_model : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointRationalTensorCanonical D l hl E
      (S.integral E) (S.rational E) (lift E) (localization E)
  /-- Rational units are obtained from the same normalized integral units. -/
  rational_unit : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointRationalTensorUnitCanonical D l hl E
      (S.integral E) (S.rational E) (lift E) (localization E)
  /-- Canonical derived field-extension tensorators. -/
  field_scalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    PointModuleScalarTensorData ι.toRingHom
      (DerivedCategory.fieldDerivedScalarExtension ι.toRingHom)
  /-- Counits are the fixed comparisons of the exact coefficient functors. -/
  field_scalar_counit : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    (field_scalar E L ι).counit =
      (ModuleCat.extendScalars.{u, u, u} ι.toRingHom).mapDerivedCategoryFactors.hom
  /-- The rational cross-field square uses the recorded scalar comparison. -/
  rational_scalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    PointRationalTensorScalarSquare D l hl E L ι (S.integral E) (S.integral L)
      (S.rational E) (S.rational L) (field_scalar E L ι)
  /-- Tensorator for extending any finite coefficient stage to Ω. -/
  stage_scalar : ∀ L : Padic.FiniteCoefficientFields l Ω,
    PointModuleScalarTensorData (pointTensorStageEmbedding l Ω L)
      (DerivedCategory.fieldDerivedScalarExtension (pointTensorStageEmbedding l Ω L))
  /-- The stage scalar counit is also the specified exact-functor comparison. -/
  stage_scalar_counit : ∀ L : Padic.FiniteCoefficientFields l Ω,
    (stage_scalar L).counit =
      (ModuleCat.extendScalars.{u, u, u}
        (pointTensorStageEmbedding l Ω L)).mapDerivedCategoryFactors.hom
  /-- The closed coefficient comparison is canonical at every common finite stage. -/
  qbar_model : PointQbarTensorCanonical D l hl Ω S stage_scalar
  /-- Its unit is the scalar extension of the actual rational coefficient unit. -/
  qbar_unit : PointQbarTensorUnitCanonical D l hl Ω S
    (stage_scalar (Padic.finiteCoefficientBase l Ω))

/-- The geometric-point fibre preserves derived tensor, canonically and coherently,
at all four coefficient stages, with coefficient units and actual reduction and
scalar-extension squares.
Source: Stacks Project Tag 07A4, lemma-pullback-tensor-product, and the coefficient
constructions of the three recorded statement dependencies
(blueprint: lem-sf-point-fibre-derived-tensor).

Proof: the identity geometric point is initial among pointed neighbourhoods, so its
inverse image is final-object sections. Its finite coefficient ring is A and its
completed integral ring is O_E. Sections is exact. On K-flat flat-term complexes
the ringed-point tensor comparison is the total pure-tensor map specified above.
It respects the signed differential, associators, braiding, coefficient unit and
unitors on generators, and descends naturally to derived categories. Finite-Tor
constructibility is closed under this tensor. Sections preserves sectionwise
countable products and the two-coordinate shifted cone of 1 minus transition.
The integral inverse comparison is consequently the completion map with quotient
tensor first coordinate and zero shifted coordinate, precisely the stated model.
The two fibre complexes have bounded finitely generated cohomology over the DVR,
so admit bounded finite-projective models. Their tensor is again bounded finite
projective. Each term is a summand of a finite free module, hence complete for the
uniformizer filtration. Quotient transitions are surjective; the map 1 minus
transition on the product is surjective with kernel this inverse limit. Thus the
completion map to the Roos complex is a quasi-isomorphism. Rationalize this map
using the balanced scalar tensorator and descend the specified coefficient/carrier
lift. Over Ω form the same comparison at every common finite stage. The recorded
stage transports and rational scalar comparison identify these formulas on larger
fields. All quotient and scalar squares hold on pure tensor generators; the full
Roos-coordinate equations preserve them under completion. Inverses and localization
preserve the unit, associator and braiding equations, giving the stated coherent
family, its canonical normalizations, and every displayed cross-stage square. -/
theorem pointFibreDerivedTensor
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    ∃ S : PointFibreDerivedTensorSystem D l hl Ω,
      Nonempty (PointFibreDerivedTensorCanonical D l hl Ω S) := by
  sorry

end WeilConjectures
