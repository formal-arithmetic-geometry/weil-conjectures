/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import all Sheaf.Paper.CompletedIntegralFiniteFree
import all Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralPrincipalCompletionComparison
import all Sheaf.Algebra.Homology.FiniteFreeCompletionExchange
import Sheaf.Algebra.Homology.PrincipalQuotientCompletionExists
import Sheaf.Algebra.Homology.FiniteFreeQuotientRoosComparison
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact

/-! # Finite-free scalar extension and the actual integral completion unit

Source: Stacks Tag 0941 and finite-free tensor/product interchange.
(blueprint: lem-pur-integral-scalar-completion-unit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  IntegralOnSlice.completion IntegralOnSlice.completionUnit completedCoefficientMap

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsCommHasDerivedCategory integralOperationsSiteSmall
  integralOperationsAbLocallyBijective integralOperationsAbSheafify
  PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective
attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] IntegralOnSlice.completionComparison
  CategoryTheory.PrincipalQuotientCompletion.quotientRoos
open Opposite
open scoped ChangeOfRings

private local instance comparisonSiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{u} _

private local instance comparisonAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance comparisonAbLocallyBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

private theorem scalar_unit_comparison
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) (A : C ⥤ C) (B : D ⥤ D)
    (u : 𝟭 C ⟶ A) (v : 𝟭 D ⟶ B) (Q : C)
    (CR : C ⥤ C) (CS : D ⥤ D)
    (uR : 𝟭 C ⟶ CR) (uS : 𝟭 D ⟶ CS)
    (ε : CR ⋙ T ≅ T ⋙ CS)
    (hε : T.map (uR.app Q) ≫ ε.hom.app Q = uS.app (T.obj Q))
    (a : CR.obj Q ≅ A.obj Q) (ha : uR.app Q ≫ a.hom = u.app Q)
    (b : CS.obj (T.obj Q) ≅ B.obj (T.obj Q))
    (hb : uS.app (T.obj Q) ≫ b.hom = v.app (T.obj Q)) :
    ∃ χ : T.obj (A.obj Q) ≅ B.obj (T.obj Q),
      T.map (u.app Q) ≫ χ.hom = v.app (T.obj Q) := by
  let χ : T.obj (A.obj Q) ≅ B.obj (T.obj Q) :=
    (T.mapIso a).symm ≪≫ ε.app Q ≪≫ b
  have hχ : T.map (u.app Q) ≫ χ.hom = v.app (T.obj Q) := by
    simp only [χ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
    rw [← ha, T.map_comp]
    simp only [Category.assoc, ← T.map_comp_assoc, a.hom_inv_id, T.map_id,
      Category.id_comp]
    erw [← Category.assoc, hε]
    exact hb
  exact ⟨χ, hχ⟩

/-- Finite-free scalar extension commutes with completion, normalized
by its unit. Source: Stacks 0941 and finite-free tensor/product interchange;
(blueprint: lem-pur-integral-scalar-completion-unit-comparison).
Proof: use one integral basis to commute tensor with both countable products of
the Roos cone. The quotient balancing maps identify its target with the full
F-adic tower, followed by the arithmetic cofinality comparison. This preserves
the augmentation. No faithfulness of finite evaluation is used. -/
theorem integralScalarCompletionUnitComparison (W : Scheme.{u}) :
    letI : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{u} _
    letI : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
      integralCoefficientAbSheafify.{u, u} W
    letI : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      integralCoefficientAbLocallyBijective.{u, u} W
    ∀ Q : DerivedCategory (scalarReductionSource.{u, u} l E W),
    ∃ χ : (pbcDerivedExtend.{u} (completedCoefficientMap.{u, u} l E F i W)).obj
          ((IntegralOnSlice.completion.{u, u} l E W none).obj Q) ≅
        (IntegralOnSlice.completion.{u, u} l F W none).obj
          ((pbcDerivedExtend.{u} (completedCoefficientMap.{u, u} l E F i W)).obj Q),
      (pbcDerivedExtend.{u} (completedCoefficientMap.{u, u} l E F i W)).map
          ((IntegralOnSlice.completionUnit.{u, u} l E W none).app Q) ≫ χ.hom =
        (IntegralOnSlice.completionUnit.{u, u} l F W none).app
          ((pbcDerivedExtend.{u} (completedCoefficientMap.{u, u} l E F i W)).obj Q) := by
  intro Q
  classical
  let H := completedScalarCochainModel.{u, u} l E F i W
  let A := IntegralOnSlice.completion.{u, u} l E W none
  let B := IntegralOnSlice.completion.{u, u} l F W none
  have hT : H.T = pbcDerivedExtend.{u} (completedCoefficientMap.{u, u} l E F i W) := by
    rfl
  erw [← hT]
  have hfree := completedIntegralFiniteFree.{u, u} l E W F i
    (completedCoefficientMap.{u, u} l E F i W) (completedCoefficientMap_projection.{u, u} l E F i W)
  have hf : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology W)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (completedCoefficientMap.{u, u} l E F i W))).obj
          (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l F W)) ≅
        ∐ (fun _ : Fin d ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E W))) := by
    let f : Fin (completedScalarRelativeDegree.{u} l E F i) → integralTowerModules l E W :=
      fun _ ↦ SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E W)
    let : HasBiproduct f :=
      (Abelian.hasFiniteBiproducts (C := integralTowerModules l E W)).out _ |>.has_biproduct f
    obtain ⟨b⟩ := hfree
    exact ⟨completedScalarRelativeDegree.{u} l E F i, ⟨b ≪≫ biproductIso f⟩⟩
  obtain ⟨uS, e, he, hu, hr⟩ := scalar_ramification.{u, u} l E F i W
  let : HasExactLimitsOfShape (Discrete ℕ) (integralTowerModules l E W) :=
    ProEt.products_exact.{u, u, 0} W (completedIntegralCoefficientSheafUnrestricted.{u, u} l E W) ℕ
  let : HasExactLimitsOfShape (Discrete ℕ) (integralTowerModules l F W) :=
    ProEt.products_exact.{u, u, 0} W (completedIntegralCoefficientSheafUnrestricted.{u, u} l F W) ℕ
  obtain ⟨CR⟩ := CategoryTheory.PrincipalQuotientCompletion.nonempty_model
    (completedIntegralCommRingSheafUnrestricted.{u, u} l E W)
    (PrincipalKoszulStrictReplacement.uniformizer.{u, u} l E W)
  obtain ⟨CS⟩ := CategoryTheory.PrincipalQuotientCompletion.nonempty_model
    (completedIntegralCommRingSheafUnrestricted.{u, u} l F W)
    (PrincipalKoszulStrictReplacement.uniformizer.{u, u} l F W)
  obtain ⟨D⟩ := CategoryTheory.PrincipalQuotientCompletion.finiteFreeQuotientRoosComparison H hf
    (PrincipalKoszulStrictReplacement.uniformizer.{u, u} l E W)
    (PrincipalKoszulStrictReplacement.uniformizer.{u, u} l F W) uS hu e he hr
  obtain ⟨ε, hε, _⟩ := CategoryTheory.PrincipalQuotientCompletion.exchangeFromCochains H
    (PrincipalKoszulStrictReplacement.uniformizer.{u, u} l E W)
    (PrincipalKoszulStrictReplacement.uniformizer.{u, u} l F W) e D CR CS
  obtain ⟨a, ha⟩ := principalIntegralCompletionComparison l E W CR Q
  obtain ⟨b, hb⟩ := principalIntegralCompletionComparison l F W CS (H.T.obj Q)
  exact scalar_unit_comparison H.T A B (IntegralOnSlice.completionUnit.{u, u} l E W none)
    (IntegralOnSlice.completionUnit.{u, u} l F W none) Q CR.completion CS.completion
    CR.unit CS.unit ε (hε Q) a ha b hb


end WeilConjectures
