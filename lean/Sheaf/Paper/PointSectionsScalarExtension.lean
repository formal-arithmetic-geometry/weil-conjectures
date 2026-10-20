/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.IntegralScalarExtension
public import Sheaf.Paper.DerivedCompleteIntegralDetailed
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntegralScalarExtensionConstructible
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic

/-! # Sections of the geometric point and integral coefficient extension

Source: blueprint `def-weil-finite-coefficient-point`, final paragraph;
Bhatt--Scholze, Lemmas 4.2.12, 6.8.2(1), Definition 3.4.10 and Lemma 3.4.12
(blueprint: lem-weil-point-sections-scalar-extension).

All tensors on coefficient modules below are ordinary termwise tensors. The
sections-tensor arrow is fixed on pure tensors, and the derived arrow is fixed
on every K-flat flat-term representative. Completion uses the recorded strict
zero-homotopy comparison, rather than an unspecified derived-limit lift.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures

variable (k : Type u) [Field k] [IsAlgClosed k]
  (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The recorded abelian sheafification at the point's actual module size.
Source: Stacks 03DA (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance (priority := 5000) pointScalarAbSheafify :
    HasSheafify (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} (Spec (.of k))

/-- The recorded locally bijective criterion at the point's actual module size.
Source: Stacks 03DA (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance (priority := 5000) pointScalarAbLocallyBijective :
    (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} (Spec (.of k))

/-- Standard localization of coefficient-module complexes in the section universe.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointScalarModuleDerived (A : Type u) [Ring A] :
    HasDerivedCategory (ModuleCat.{u + 1} A) := HasDerivedCategory.standard _

/-- Standard localization for modules on the point in their actual section universe.
Source: Stacks 05RU (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedSheafDerived
    (R : Sheaf (Scheme.ProEt.topology (Spec (.of k))) RingCat.{u + 1}) :
    HasDerivedCategory (SheafOfModules.{u + 1} R) := HasDerivedCategory.standard _

/-- The canonical constant-section coefficient map at the final object, obtained
from the recorded constant-to-completion morphism and sheafification unit.
Source: Bhatt--Scholze 6.8.2(1); blueprint completed coefficients, order 1455
(blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointCompletedConstant :
    Padic.coefficientExtensionIntegers l E →+*
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k))).obj.obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) :=
  (((integralConstantToCompletion l E (Spec (.of k))).hom.app
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))).hom).comp
      ((((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((toSheafify (Scheme.ProEt.topology (Spec (.of k)))
          ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))).app
              (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))).hom).comp
                ULift.ringEquiv.symm.toRingHom)

/-- Evaluation, with coefficients restricted along the actual constant-section map.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointCompletedSections :
    integralTowerModules.{u, u} l E (Spec (.of k)) ⥤
      ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) :=
  SheafOfModules.evaluation.{u + 1}
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k)))
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) ⋙
    ModuleCat.restrictScalars (pointCompletedConstant k l E)

/-- Exactness and additivity of completed integral sections.
Source: exact point-sections node and blueprint final paragraph
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: point evaluation is exact by lem-weil-point-proetale-sections-exact.
Restriction of scalars leaves the underlying abelian group unchanged, so preserves
kernels and cokernels. Both functors add maps sectionwise. -/
theorem pointCompletedSections_exact :
    (pointCompletedSections k l E).Additive ∧
      PreservesFiniteLimits (pointCompletedSections k l E) ∧
      PreservesFiniteColimits (pointCompletedSections k l E) := by
  sorry

/-- Additivity supplied by exact evaluation.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedSectionsAdditive :
    (pointCompletedSections k l E).Additive := (pointCompletedSections_exact k l E).1

/-- Finite-limit preservation supplied by exact evaluation.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedSectionsLimits :
    PreservesFiniteLimits (pointCompletedSections k l E) :=
  (pointCompletedSections_exact k l E).2.1

/-- Finite-colimit preservation supplied by exact evaluation.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedSectionsColimits :
    PreservesFiniteColimits (pointCompletedSections k l E) :=
  (pointCompletedSections_exact k l E).2.2

/-- Termwise completed sections, descended through derived localization.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointCompletedDerivedSections :
    DerivedCategory (integralTowerModules.{u, u} l E (Spec (.of k))) ⥤
      DerivedCategory (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) :=
  (pointCompletedSections k l E).mapDerivedCategory

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Ordinary tensor with the valuation ring of the larger coefficient field.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointIntegralModuleTensor :=
  ModuleCat.extendScalars.{u, u, u + 1} (integralScalarIntegerInclusion.{u} l E L ι)

/-- The ordinary module tensor and fraction-field tensor functors are exact and additive.
Source: Bhatt--Scholze 6.8.2(1), blueprint final paragraph
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: O_L is finite free over O_E, so tensor is a finite direct sum, hence exact.
The fraction field of a valuation DVR is its localization at nonzero elements;
localization preserves kernels and cokernels. The tensor maps add termwise. -/
theorem pointCoefficientTensors_exact :
    ((pointIntegralModuleTensor l E L ι).Additive ∧
      PreservesFiniteLimits (pointIntegralModuleTensor l E L ι) ∧
      PreservesFiniteColimits (pointIntegralModuleTensor l E L ι)) ∧
    ((ModuleCat.extendScalars.{u, u, u + 1}
      (algebraMap (Padic.coefficientExtensionIntegers l E) E)).Additive ∧
      PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1}
        (algebraMap (Padic.coefficientExtensionIntegers l E) E)) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u + 1}
        (algebraMap (Padic.coefficientExtensionIntegers l E) E))) := by
  sorry

/-- Additivity of the ordinary integral tensor.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointIntegralModuleTensorAdditive :
    (pointIntegralModuleTensor l E L ι).Additive :=
  (pointCoefficientTensors_exact l E L ι).1.1

/-- Exactness at kernels of the ordinary integral tensor.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointIntegralModuleTensorLimits :
    PreservesFiniteLimits (pointIntegralModuleTensor l E L ι) :=
  (pointCoefficientTensors_exact l E L ι).1.2.1

/-- Exactness at cokernels of the ordinary integral tensor.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointIntegralModuleTensorColimits :
    PreservesFiniteColimits (pointIntegralModuleTensor l E L ι) :=
  (pointCoefficientTensors_exact l E L ι).1.2.2

/-- Ordinary termwise integral tensor on module derived categories.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointIntegralModuleDerivedTensor :=
  (pointIntegralModuleTensor l E L ι).mapDerivedCategory

/-- The sections-tensor map is uniquely fixed by its balanced pure-tensor formula.
Source: Bhatt--Scholze 6.8.2(1), blueprint final paragraph
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: send a tensor n to the sheafified tensor of the constant section a with n.
The coefficient maps agree on every finite quotient, so balancing is valid.
The sheaf tensor universal property gives the map. Pure tensors generate its
source, proving uniqueness, and the same formula commutes with every sheaf map.
A finite free basis of R_L over R_E gives a global O_E-basis of O_L by evaluating
at the point; both sides are then the same finite sum of sections. -/
theorem pointSectionsTensor_existsUnique :
    ∃! θ : pointCompletedSections k l E ⋙ pointIntegralModuleTensor l E L ι ≅
        completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)) ⋙
          pointCompletedSections k l L,
      ∀ (F : integralTowerModules.{u, u} l E (Spec (.of k)))
        (a : Padic.coefficientExtensionIntegers l L)
        (n : (pointCompletedSections k l E).obj F),
        θ.hom.app F (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion.{u} l E L ι] n) =
          completedScalarTensorSection.{u, u} l E L ι (Spec (.of k)) F
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) (pointCompletedConstant k l L a) n := by
  sorry

/-- The canonical balanced sections-tensor transformation.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointSectionsTensor :=
  (pointSectionsTensor_existsUnique k l E L ι).exists.choose

/-- Finite-free ordinary completed coefficient extension is exact.
Source: Bhatt--Scholze 6.8.2(1)
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: choose a finite free R_E-basis of R_L. Ordinary sheafified tensor is then
naturally a finite direct sum on the underlying R_E-modules. Finite sums are exact,
and restriction of scalars detects exactness. -/
theorem pointCompletedOrdinary_exact :
    PreservesFiniteLimits (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))) ∧
      PreservesFiniteColimits (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))) := by
  sorry

/-- Preservation of kernels by finite-free coefficient extension.
Source: Bhatt--Scholze 6.8.2(1)
(blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedOrdinaryLimits :
    PreservesFiniteLimits (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))) :=
  (pointCompletedOrdinary_exact k l E L ι).1

/-- Preservation of cokernels by coefficient extension.
Source: Bhatt--Scholze 6.8.2(1)
(blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedOrdinaryColimits :
    PreservesFiniteColimits (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))) :=
  (pointCompletedOrdinary_exact k l E L ι).2

/-- The universal derived tensor comparison is the termwise one for a finite-free extension.
Source: Stacks 06YY and Bhatt--Scholze 6.8.2(1)
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: ordinary finite-free tensor preserves every quasi-isomorphism, not only those
between K-flat complexes. Its exact-functor localization is therefore its left derived
functor. The universal counit gives the displayed comparison, and localization at
quasi-isomorphisms makes the normalization on representatives determine it uniquely. -/
theorem pointOrdinaryDerivedComparison_existsUnique :
    ∃! δ : completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k)) ≅
        (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))).mapDerivedCategory,
      ∀ P : CochainComplex (integralTowerModules.{u, u} l E (Spec (.of k))) ℤ,
        δ.hom.app (DerivedCategory.Q.obj P) ≫
          (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of
        k))).mapDerivedCategoryFactors.hom.app P =
            completedScalarCounit.{u, u} l E L ι (Spec (.of k)) P := by
  sorry

/-- The canonical identification of ordinary derived and termwise tensor.
Source: Stacks 06YY (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointOrdinaryDerivedComparison :=
  (pointOrdinaryDerivedComparison_existsUnique k l E L ι).exists.choose

/-- The derived sections-tensor isomorphism, normalized by actual termwise tensors.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointDerivedSectionsTensor :
    pointCompletedDerivedSections k l E ⋙ pointIntegralModuleDerivedTensor l E L ι ≅
      completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k)) ⋙
        pointCompletedDerivedSections k l L :=
  (Functor.mapDerivedCategoryCompIso
    (pointCompletedSections k l E) (pointIntegralModuleTensor l E L ι)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointSectionsTensor k l E L ι) ≪≫
    Functor.mapDerivedCategoryCompIso
      (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)))
      (pointCompletedSections k l L) ≪≫
    Functor.isoWhiskerRight (pointOrdinaryDerivedComparison k l E L ι).symm
      (pointCompletedDerivedSections k l L)

/-- Multiplication on ordinary sheaf tensor fixes the identity-extension identification.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: multiplication s tensor x to sx is balanced and inverse to x to 1 tensor x.
These formulas commute with restrictions and sheaf maps, and tensors generate,
so they determine exactly one natural isomorphism. -/
theorem pointOrdinaryTensorUnit_existsUnique :
    ∃! μ : completedOrdinaryScalarExtension.{u, u} l E E (AlgHom.id ℚ_[l] E) (Spec (.of k)) ≅
        𝟭 (integralTowerModules.{u, u} l E (Spec (.of k))),
      ∀ (F : integralTowerModules.{u, u} l E (Spec (.of k))) (U : (Spec (.of k)).ProEtᵒᵖ)
        (a : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k))).obj.obj U)
        (x : F.val.obj U),
        (μ.hom.app F).val.app U
          (completedScalarTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) (Spec (.of k)) F U a x) =
            a • x := by
  sorry

/-- The canonical ordinary multiplication isomorphism.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointOrdinaryTensorUnit :=
  (pointOrdinaryTensorUnit_existsUnique k l E).exists.choose

/-- The canonical derived multiplication isomorphism.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointDerivedTensorUnit :
    completedDerivedScalarExtension.{u, u} l E E (AlgHom.id ℚ_[l] E) (Spec (.of k)) ≅
      𝟭 (DerivedCategory (integralTowerModules.{u, u} l E (Spec (.of k)))) :=
  pointOrdinaryDerivedComparison k l E E (AlgHom.id ℚ_[l] E) ≪≫
    Functor.mapDerivedCategoryNatIso (pointOrdinaryTensorUnit k l E) ≪≫
    Functor.mapDerivedCategoryIdIso _

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (κ : L →ₐ[ℚ_[l]] M)

/-- The balanced sheaf-tensor associator is fixed on all iterated pure tensors.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: send b tensor (a tensor x) to b*iota(a) tensor x. Balancing proves that
this is well defined; its inverse sends c tensor x to c tensor (1 tensor x).
The two composites are identities on generators. These maps respect restrictions
and all sheaf morphisms, and their generator formulas imply uniqueness. -/
theorem pointOrdinaryTensorAssoc_existsUnique :
    ∃! α : completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)) ⋙
        completedOrdinaryScalarExtension.{u, u} l L M κ (Spec (.of k)) ≅
        completedOrdinaryScalarExtension.{u, u} l E M (κ.comp ι) (Spec (.of k)),
      ∀ (F : integralTowerModules.{u, u} l E (Spec (.of k))) (U : (Spec (.of k)).ProEtᵒᵖ)
        (a : (completedIntegralCommRingSheafUnrestricted.{u, u} l L (Spec (.of k))).obj.obj U)
        (b : (completedIntegralCommRingSheafUnrestricted.{u, u} l M (Spec (.of k))).obj.obj U)
        (x : F.val.obj U),
        (α.hom.app F).val.app U
          (completedScalarTensorSection.{u, u} l L M κ (Spec (.of k))
            ((completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))).obj F) U b
            (completedScalarTensorSection.{u, u} l E L ι (Spec (.of k)) F U a x)) =
          completedScalarTensorSection.{u, u} l E M (κ.comp ι) (Spec (.of k)) F U
            (b * (completedCoefficientMap.{u, u} l L M κ (Spec (.of k))).hom.app U a) x := by
  sorry

/-- The canonical ordinary tensor associator.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointOrdinaryTensorAssoc :=
  (pointOrdinaryTensorAssoc_existsUnique k l E L ι M κ).exists.choose

/-- The ordinary derived tensor associator, descended from the balanced maps.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointDerivedTensorAssoc :
    completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k)) ⋙
      completedDerivedScalarExtension.{u, u} l L M κ (Spec (.of k)) ≅
      completedDerivedScalarExtension.{u, u} l E M (κ.comp ι) (Spec (.of k)) :=
  Functor.isoWhiskerRight (pointOrdinaryDerivedComparison k l E L ι) _ ≪≫
    Functor.isoWhiskerLeft _ (pointOrdinaryDerivedComparison k l L M κ) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)))
      (completedOrdinaryScalarExtension.{u, u} l L M κ (Spec (.of k)))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointOrdinaryTensorAssoc k l E L ι M κ) ≪≫
    (pointOrdinaryDerivedComparison k l E M (κ.comp ι)).symm

/-- The module multiplication isomorphism, for the actual identity integer inclusion.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: a tensor n maps to an; n maps to 1 tensor n. Balancing gives the two inverse
identities, naturality follows on generators, and the formula determines the map. -/
theorem pointIntegralModuleUnit_existsUnique :
    ∃! μ : pointIntegralModuleTensor l E E (AlgHom.id ℚ_[l] E) ≅
        𝟭 (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)),
      ∀ (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (a : Padic.coefficientExtensionIntegers l E) (n : N),
        μ.hom.app N (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion.{u} l E E (AlgHom.id ℚ_[l] E)] n) = a • n := by
  sorry

/-- Ordinary multiplication on integral module complexes after localization.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointIntegralModuleDerivedUnit :
    pointIntegralModuleDerivedTensor l E E (AlgHom.id ℚ_[l] E) ≅
      𝟭 (DerivedCategory (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  Functor.mapDerivedCategoryNatIso
    (pointIntegralModuleUnit_existsUnique l E).exists.choose ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The module associator is the ordinary balanced multiplication of coefficient factors.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: send b tensor (a tensor n) to b*kappa(a) tensor n, with inverse c tensor n
to c tensor (1 tensor n). Balancing proves the inverse identities and naturality;
generators determine the map uniquely. -/
theorem pointIntegralModuleAssoc_existsUnique :
    ∃! α : pointIntegralModuleTensor l E L ι ⋙ pointIntegralModuleTensor l L M κ ≅
        pointIntegralModuleTensor l E M (κ.comp ι),
      ∀ (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (a : Padic.coefficientExtensionIntegers l L)
        (b : Padic.coefficientExtensionIntegers l M) (n : N),
        α.hom.app N
          (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
            integralScalarIntegerInclusion.{u} l L M κ]
            (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              integralScalarIntegerInclusion.{u} l E L ι] n)) =
          (b * integralScalarIntegerInclusion.{u} l L M κ a) ⊗ₜ[
            Padic.coefficientExtensionIntegers l E,
            integralScalarIntegerInclusion.{u} l E M (κ.comp ι)] n := by
  sorry

/-- The ordinary module-complex associator in the derived category.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointIntegralModuleDerivedAssoc :
    pointIntegralModuleDerivedTensor l E L ι ⋙ pointIntegralModuleDerivedTensor l L M κ ≅
      pointIntegralModuleDerivedTensor l E M (κ.comp ι) :=
  (Functor.mapDerivedCategoryCompIso
    (pointIntegralModuleTensor l E L ι) (pointIntegralModuleTensor l L M κ)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose

/-- Fraction-field extension on coefficient modules.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointModuleRationalization :=
  ModuleCat.extendScalars.{u, u, u + 1}
    (algebraMap (Padic.coefficientExtensionIntegers l E) E)

/-- Additivity of localization to the coefficient field.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointModuleRationalizationAdditive :
    (pointModuleRationalization l E).Additive :=
  (pointCoefficientTensors_exact l E E (AlgHom.id ℚ_[l] E)).2.1

/-- Localization preserves kernels.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointModuleRationalizationLimits :
    PreservesFiniteLimits (pointModuleRationalization l E) :=
  (pointCoefficientTensors_exact l E E (AlgHom.id ℚ_[l] E)).2.2.1

/-- Localization preserves cokernels.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointModuleRationalizationColimits :
    PreservesFiniteColimits (pointModuleRationalization l E) :=
  (pointCoefficientTensors_exact l E E (AlgHom.id ℚ_[l] E)).2.2.2

/-- Ordinary termwise tensor with the fraction field on derived modules.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointModuleDerivedRationalization :=
  (pointModuleRationalization l E).mapDerivedCategory

/-- Tensor with a coefficient field extension is exact and additive.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: a field extension is a free module, so tensor is a direct sum of copies on
underlying vector spaces and preserves kernels and cokernels. It adds maps termwise. -/
theorem pointCoefficientFieldTensor_exact :
    (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom).Additive ∧
      PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) := by
  sorry

/-- Additivity of coefficient field extension.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCoefficientFieldTensorAdditive :
    (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom).Additive :=
  (pointCoefficientFieldTensor_exact l E L ι).1

/-- Coefficient field extension preserves kernels.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCoefficientFieldTensorLimits :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) :=
  (pointCoefficientFieldTensor_exact l E L ι).2.1

/-- Coefficient field extension preserves cokernels.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCoefficientFieldTensorColimits :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) :=
  (pointCoefficientFieldTensor_exact l E L ι).2.2

/-- Termwise coefficient field extension on derived vector spaces.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointCoefficientFieldDerivedTensor :=
  (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom).mapDerivedCategory

/-- The ordinary field-complex multiplication isomorphism.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointCoefficientFieldDerivedUnit :
    pointCoefficientFieldDerivedTensor l E E (AlgHom.id ℚ_[l] E) ≅
      𝟭 (DerivedCategory (ModuleCat.{u + 1} E)) :=
  Functor.mapDerivedCategoryNatIso (ModuleCat.extendScalarsId.{u, u + 1} E) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The ordinary field-complex associator.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointCoefficientFieldDerivedAssoc :
    pointCoefficientFieldDerivedTensor l E L ι ⋙ pointCoefficientFieldDerivedTensor l L M κ ≅
      pointCoefficientFieldDerivedTensor l E M (κ.comp ι) :=
  (Functor.mapDerivedCategoryCompIso
    (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) (ModuleCat.extendScalars.{u, u, u + 1}
        κ.toRingHom)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom
        κ.toRingHom).symm

/-- Rationalization and finite extension commute by the actual balanced localization map.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: send b tensor (a tensor n) to ba tensor (1 tensor n), where a is included
in L. The inverse sends b tensor (x tensor n) to b*iota(x) tensor (1 tensor n).
All nonzero O_E-elements are units in L, so denominators move across the tensor
relation. These maps respect the balanced relations and are mutual inverses;
their formulas commute with module morphisms and determine the map uniquely. -/
theorem pointTensorRationalization_existsUnique :
    ∃! β : pointIntegralModuleTensor l E L ι ⋙ pointModuleRationalization l L ≅
        pointModuleRationalization l E ⋙ ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom,
      ∀ (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (a : Padic.coefficientExtensionIntegers l L) (b : L) (n : N),
        β.hom.app N
          (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
            algebraMap (Padic.coefficientExtensionIntegers l L) L]
            (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              integralScalarIntegerInclusion.{u} l E L ι] n)) =
          (b * (a : L)) ⊗ₜ[E, ι.toRingHom]
            ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              algebraMap (Padic.coefficientExtensionIntegers l E) E] n) := by
  sorry

/-- The canonical localization-tensor associator on module derived categories.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointDerivedTensorRationalization :
    pointIntegralModuleDerivedTensor l E L ι ⋙ pointModuleDerivedRationalization l L ≅
      pointModuleDerivedRationalization l E ⋙ pointCoefficientFieldDerivedTensor l E L ι :=
  (Functor.mapDerivedCategoryCompIso
    (pointIntegralModuleTensor l E L ι) (pointModuleRationalization l L)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (pointTensorRationalization_existsUnique l E L ι).exists.choose ≪≫
      Functor.mapDerivedCategoryCompIso
        (pointModuleRationalization l E) (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom)

section Constructible

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The algebraic closure in the fixed finite-field datum is algebraically closed.
Source: blueprint finite-field conventions
(blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointDatumIsAlgClosed : IsAlgClosed D.k :=
  IsAlgClosure.isAlgClosed D.k₀

/-- The two recorded constructibility interfaces describe the same point objects.
Source: blueprint order 1459 and the point's fixed finite-field datum
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: both predicates require derived completeness of the same completed coefficient
module complex. Identify their quotient reductions by the normalized change-of-rings
counit on K-flat representatives. These identifications preserve constructibility
and cohomological support. The support inclusion in Icc is exactly the pair of bounds
in the finite-field interface, with the same interval for every positive exponent. -/
theorem pointIntegralConstructible_iff
    (K : completedIntegralDerivedCategory l E (Spec (.of D.k)) D hl) :
    boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) K ↔
      sfIntegralConstructible l E (Spec (.of D.k)) K := by
  sorry

/-- The canonical completion comparison is invertible on the constructible integral category.
Source: Bhatt--Scholze 3.4.12 and blueprint final paragraph
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: the defining constructible predicate includes derived completeness. Its
augmented reduction tower is the same strict tower as the unrestricted predicate:
both units send x to 1 tensor x, and their product and cone maps agree. Apply
lem-weil-finite-free-completed-scalar-comparison to this complete object. -/
theorem pointConstructibleCompletionComparison_isIso
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (_hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    IsIso ((completedScalarComparison.{u, u} l E L ι
            (Spec (.of D.k))).app K) := by
  sorry

/-- The actual completion comparison as an isomorphism on an integral constructible object.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointConstructibleCompletionIso
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (completedDerivedScalarExtension.{u, u} l E L ι
            (Spec (.of D.k))).obj K ≅
      (integralScalarExtension.{u} l E L ι
            (Spec (.of D.k))).obj K :=
  letI := pointConstructibleCompletionComparison_isIso l E L ι D hl K hK
  asIso ((completedScalarComparison.{u, u} l E L ι
            (Spec (.of D.k))).app K)

/-- Phi is precisely the inverse of sections of chi after the canonical sections-tensor map.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointSectionsScalarExtensionIso
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (pointCompletedDerivedSections D.k l L).obj
        ((integralScalarExtension.{u} l E L ι
            (Spec (.of D.k))).obj K) ≅
      (pointIntegralModuleDerivedTensor l E L ι).obj
        ((pointCompletedDerivedSections D.k l E).obj K) :=
  ((pointDerivedSectionsTensor D.k l E L ι).app K ≪≫
    (pointCompletedDerivedSections D.k l L).mapIso
      (pointConstructibleCompletionIso l E L ι D hl K hK)).symm

/-- The integral identity identification is completeness inverted followed by multiplication.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointIntegralScalarUnit
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (integralScalarExtension.{u} l E E (AlgHom.id ℚ_[l] E)
            (Spec (.of D.k))).obj K ≅ K :=
  (pointConstructibleCompletionIso l E E (AlgHom.id ℚ_[l] E) D hl K hK).symm ≪≫
    (pointDerivedTensorUnit D.k l E).app K

/-- The integral associator is the specified conjugate of the ordinary derived associator.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointIntegralScalarAssoc
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (integralScalarExtension.{u} l L M κ
            (Spec (.of D.k))).obj
        ((integralScalarExtension.{u} l E L ι
            (Spec (.of D.k))).obj K) ≅
      (integralScalarExtension.{u} l E M (κ.comp ι)
            (Spec (.of D.k))).obj K :=
  (pointConstructibleCompletionIso l L M κ D hl _
    (integralScalarExtension_constructible D l hl E L ι
      (Spec (.of D.k)) ⟨K, hK⟩)).symm ≪≫
    (completedDerivedScalarExtension.{u, u} l L M κ
            (Spec (.of D.k))).mapIso
      (pointConstructibleCompletionIso l E L ι D hl K hK).symm ≪≫
    (pointDerivedTensorAssoc D.k l E L ι M κ).app K ≪≫
    pointConstructibleCompletionIso l E M (κ.comp ι) D hl K hK

/-- Rational phi is integral phi tensored with L, followed by the balanced localization map.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointRationalSectionsScalarExtensionIso
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (pointModuleDerivedRationalization l L).obj
        ((pointCompletedDerivedSections D.k l L).obj
          ((integralScalarExtension.{u} l E L ι
            (Spec (.of D.k))).obj K)) ≅
      (pointCoefficientFieldDerivedTensor l E L ι).obj
        ((pointModuleDerivedRationalization l E).obj
          ((pointCompletedDerivedSections D.k l E).obj K)) :=
  (pointModuleDerivedRationalization l L).mapIso
    (pointSectionsScalarExtensionIso l E L ι D hl K hK) ≪≫
      (pointDerivedTensorRationalization l E L ι).app
        ((pointCompletedDerivedSections D.k l E).obj K)

/-- Sections commute with integral scalar extension, naturally, with identity and tower
coherence; tensoring with L yields the same assertions after rationalization.
The isomorphisms in this statement are the named canonical constructions above.
Source: blueprint `def-weil-finite-coefficient-point`, final paragraph
(blueprint: lem-weil-point-sections-scalar-extension).

Proof:
1. Apply the continuous-coefficient description at Spec k. Evaluation on its one-point
space identifies completed coefficient sections with O_F, compatibly with inclusions
and all quotient projections. A finite free R_E-basis of R_L therefore evaluates to
an O_E-basis of O_L; the completed sheaf is not replaced by the discrete constant one.
2. The balanced map a tensor n to the sheafified tensor of a and n is the identity
on the coordinates of this basis. It is O_L-linear, natural, and commutes with each
differential. Both tensor functors are finite sums and exact. Exact point sections
preserve quasi-isomorphisms, so these comparisons descend to derived categories.
3. Choose a K-flat flat-term representative. The ordinary derived tensor counit and
the strict completion comparison identify its localized comparison with theta followed
by sections of chi. Completeness makes chi invertible; phi is their inverse. For a
roof, use naturality on both chain maps and invert the quasi-isomorphism. This proves
naturality for every derived morphism and independence of representatives.
4. For a tower E to L to M, the ordinary associator sends b tensor (a tensor x)
to b*kappa(a) tensor x, and its inverse sends c tensor x to c tensor (1 tensor x).
Constructibility of the first extension allows the second completion comparison.
Conjugating by the three comparisons gives exactly pointIntegralScalarAssoc.
For the identity extension, the comparison is the completeness unit after multiplication.
5. Both sections-tensor composites send the iterated pure tensor to the section
with coefficient product ab. Insert the four completion comparisons in the conjugate
associator; naturality moves chi past theta and each chi inverse cancels chi. Invert
the resulting equation to obtain the displayed integral composition equation. The unit
calculation sends a tensor n to an and gives the displayed identity equation.
6. Tensor integral phi with L. The balanced localization maps send coefficient
factors to their product. Nonzero O_E-elements are units in L, so the inverse maps
are well defined also on fractions. Localization is exact and field extension is
free, so these are derived isomorphisms. The same coefficient-product calculation,
including denominators, proves rational naturality, identity and composition. -/
theorem pointSectionsScalarExtension
    (Q : Type u) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (F G H : Padic.FiniteCoefficientFields l Q) (hFG : F ≤ G) (hGH : G ≤ H)
    (K : completedIntegralDerivedCategory l F.val
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl F.val
            (Spec (.of D.k)) K) :
    (∀ (J : completedIntegralDerivedCategory l F.val
            (Spec (.of D.k)) D hl)
      (hJ : boundedConstructibleDerivedCompleteIntegral D l hl F.val
            (Spec (.of D.k)) J)
      (f : K ⟶ J),
      (pointCompletedDerivedSections D.k l G.val).map
          ((integralScalarExtension.{u} l F.val G.val (IntermediateField.inclusion hFG)
            (Spec (.of D.k))).map f) ≫
          (pointSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion hFG) D hl J
        hJ).hom =
        (pointSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion hFG) D hl K
        hK).hom ≫
          (pointIntegralModuleDerivedTensor l F.val G.val (IntermediateField.inclusion hFG)).map
            ((pointCompletedDerivedSections D.k l F.val).map f)) ∧
    ((pointSectionsScalarExtensionIso l F.val F.val (AlgHom.id ℚ_[l] F.val) D hl K hK).hom ≫
        (pointIntegralModuleDerivedUnit l F.val).hom.app
          ((pointCompletedDerivedSections D.k l F.val).obj K) =
      (pointCompletedDerivedSections D.k l F.val).map (pointIntegralScalarUnit l F.val D hl K
        hK).hom) ∧
    ((pointCompletedDerivedSections D.k l H.val).map
        (pointIntegralScalarAssoc l F.val G.val (IntermediateField.inclusion hFG) H.val
        (IntermediateField.inclusion hGH) D hl K hK).hom ≫
        (pointSectionsScalarExtensionIso l F.val H.val ((IntermediateField.inclusion hGH).comp
        (IntermediateField.inclusion hFG)) D hl K hK).hom =
      (pointSectionsScalarExtensionIso l G.val H.val (IntermediateField.inclusion hGH) D hl _
        (integralScalarExtension_constructible D l hl F.val G.val
          (IntermediateField.inclusion hFG) (Spec (.of D.k)) ⟨K, hK⟩)).hom ≫
        (pointIntegralModuleDerivedTensor l G.val H.val (IntermediateField.inclusion hGH)).map
          (pointSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion hFG) D hl K
        hK).hom ≫
        (pointIntegralModuleDerivedAssoc l F.val G.val (IntermediateField.inclusion hFG) H.val
        (IntermediateField.inclusion hGH)).hom.app
          ((pointCompletedDerivedSections D.k l F.val).obj K)) ∧
    (∀ (J : completedIntegralDerivedCategory l F.val
            (Spec (.of D.k)) D hl)
      (hJ : boundedConstructibleDerivedCompleteIntegral D l hl F.val
            (Spec (.of D.k)) J)
      (f : K ⟶ J),
      (pointModuleDerivedRationalization l G.val).map
          ((pointCompletedDerivedSections D.k l G.val).map
            ((integralScalarExtension.{u} l F.val G.val (IntermediateField.inclusion hFG)
            (Spec (.of D.k))).map f)) ≫
          (pointRationalSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion hFG)
        D hl J hJ).hom =
        (pointRationalSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion hFG) D
        hl K hK).hom ≫
          (pointCoefficientFieldDerivedTensor l F.val G.val (IntermediateField.inclusion hFG)).map
            ((pointModuleDerivedRationalization l F.val).map
              ((pointCompletedDerivedSections D.k l F.val).map f))) ∧
    ((pointRationalSectionsScalarExtensionIso l F.val F.val (AlgHom.id ℚ_[l] F.val) D hl K hK).hom ≫
        (pointCoefficientFieldDerivedUnit l F.val).hom.app
          ((pointModuleDerivedRationalization l F.val).obj
            ((pointCompletedDerivedSections D.k l F.val).obj K)) =
      (pointModuleDerivedRationalization l F.val).map
        ((pointCompletedDerivedSections D.k l F.val).map
          (pointIntegralScalarUnit l F.val D hl K hK).hom)) ∧
    ((pointModuleDerivedRationalization l H.val).map
        ((pointCompletedDerivedSections D.k l H.val).map
          (pointIntegralScalarAssoc l F.val G.val (IntermediateField.inclusion hFG) H.val
        (IntermediateField.inclusion hGH) D hl K hK).hom) ≫
        (pointRationalSectionsScalarExtensionIso l F.val H.val ((IntermediateField.inclusion
        hGH).comp (IntermediateField.inclusion hFG)) D hl K hK).hom =
      (pointRationalSectionsScalarExtensionIso l G.val H.val (IntermediateField.inclusion hGH) D
        hl _
        (integralScalarExtension_constructible D l hl F.val G.val
          (IntermediateField.inclusion hFG) (Spec (.of D.k)) ⟨K, hK⟩)).hom ≫
        (pointCoefficientFieldDerivedTensor l G.val H.val (IntermediateField.inclusion hGH)).map
          (pointRationalSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion hFG)
        D hl K hK).hom ≫
        (pointCoefficientFieldDerivedAssoc l F.val G.val (IntermediateField.inclusion hFG) H.val
        (IntermediateField.inclusion hGH)).hom.app
          ((pointModuleDerivedRationalization l F.val).obj
            ((pointCompletedDerivedSections D.k l F.val).obj K))) := by
  sorry

end Constructible

end WeilConjectures
