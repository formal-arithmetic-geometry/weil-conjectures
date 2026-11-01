/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitTensorSystemData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Multiplication on the regular single coefficient system

The multiplication is constructed before derived localization, as the left
unitor of the actual total-complex tensor, and transported by the specified
K-flat tensor comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

local instance regularUnitModulesMonoidal (W : Scheme.{u}) :
    MonoidalCategory (coefficientSequenceModules l E W) :=
  SheafOfModules.cochainModulesMonoidal (coefficientSequenceCommRingSheaf l E W)

local instance regularUnitTensorLeftColimits (W : Scheme.{u})
    (M : coefficientSequenceModules l E W) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  SheafOfModules.cochainTensorLeftPreservesColimits
    (coefficientSequenceCommRingSheaf l E W) M

local instance regularUnitTensorRightColimits (W : Scheme.{u})
    (M : coefficientSequenceModules l E W) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  SheafOfModules.cochainTensorRightPreservesColimits
    (coefficientSequenceCommRingSheaf l E W) M

/-- The actual regular unit complex is K-flat, since tensoring with it has the
natural right unitor. Source: Stacks 06YN.
(blueprint: def-pur-completed-unit-regular-multiplication). -/
theorem regularUnitComplex_kFlat (W : Scheme.{u}) :
    CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W)
      (ringedTensorUnitComplex.{u + 1, u, u} _ (coefficientSequenceCommRingSheaf l E W)) := by
  intro Z hZ i
  exact (hZ i).of_iso (ρ_ Z).symm

/-- Ordinary multiplication of two regular unit complexes.
Source: Stacks 07A4, the ordinary scalar unitor.
(blueprint: def-pur-completed-unit-regular-multiplication). -/
def regularUnitComplex_multiplication (W : Scheme.{u}) :
    (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj
      (ringedTensorUnitComplex.{u + 1, u, u} _ (coefficientSequenceCommRingSheaf l E W),
       ringedTensorUnitComplex.{u + 1, u, u} _ (coefficientSequenceCommRingSheaf l E W)) ≅
      ringedTensorUnitComplex.{u + 1, u, u} _ (coefficientSequenceCommRingSheaf l E W) :=
  λ_ _

/-- Derived regular multiplication, transported by the fixed simultaneous K-flat model.
Source: Stacks 07A4 and 0941.
(blueprint: def-pur-completed-unit-regular-multiplication). -/
def regularSystemMultiplication (W : Scheme.{u}) :
    (pullbackTensorCalculus l E W).systemClosed.tensor.obj
      (systemObject l E W, systemObject l E W) ≅ systemObject l E W :=
  ((pullbackTensorCalculus l E W).systemTensorModel.iso
    (coefficientSequenceTopology (Scheme.ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)
    (pullbackTensorCalculus l E W).systemClosed _ _
    (regularUnitComplex_kFlat l E W) (regularUnitComplex_kFlat l E W)).symm ≪≫
    DerivedCategory.Q.mapIso (regularUnitComplex_multiplication l E W)

end WeilConjectures.CompletedUnitPullback
