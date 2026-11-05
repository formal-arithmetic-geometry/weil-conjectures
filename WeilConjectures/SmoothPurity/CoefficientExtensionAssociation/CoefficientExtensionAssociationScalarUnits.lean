/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientScalarCochainEvaluation
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryStrictTensor

/-! # Scalar unit sections and finite evaluation

Source: Stacks 03D7 and the sequence-site construction preceding 0941.
Native target carriers keep presheaf maps and adjunction sections small while
their proved comparison lemmas retain the actual restriction-of-scalars maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace CoefficientExtensionAssociation
section BalancedUnitMap
universe c v r
@[irreducible] private def abstractUnitSection
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    {F : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S}
    (adj : F ⊣ SheafOfModules.restrictScalars φ)
    (M : SheafOfModules.{r} R) (U : Cᵒᵖ) (x : M.val.obj U) :
    (F.obj M).val.obj U := (adj.unit.app M).val.app U x

@[irreducible] private def presheafMapSection
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} (M : SheafOfModules.{r} R)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U) : M.val.obj V := M.val.map f x

end BalancedUnitMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  integralScalarReduction completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.leftAdjoint SemilinearSections.systemMap
  scalarReductionExtension scalarReductionExistence coefficientOrdinaryQuotient
  coefficientQuotientNatTrans coefficientOrdinaryQuotientComponent

/-- The unit section of finite scalar extension, in its native target module.
Source: Stacks 03D7. -/
@[irreducible] def finiteScalarUnitSection
    (A : CoefficientExtensionSystems l E L ι W)
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    ((A.levels n).model.E.obj ((coefficientSequenceEvaluation l E W n).obj N)).val.obj U :=
  ((A.levels n).ordinaryAdjunction.unit.app
    ((coefficientSequenceEvaluation l E W n).obj N)).val.app U x

/-- The finite scalar unit transported back through the supplied evaluation isomorphism.
Source: Stacks 03D7 and the ordinary evaluation unit equation. -/
@[irreducible] def evaluatedUnitSection
    (A : CoefficientExtensionSystems l E L ι W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    ((coefficientSequenceEvaluation l L W n).obj (A.scalar.model.E.obj N)).val.obj U :=
  ((ρ n).inv.app N).val.app U (finiteScalarUnitSection l E L ι W A N n U x)

@[irreducible] private def scalarSystemMap :
    ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E W)) ⟶
    ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l L W)) :=
  (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (SemilinearSections.systemMap.{t + 1, t, max (t + 1) u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
        (integralScalarQuotientSheafMap l E L ι W)
        (coefficientExtensionQuotient_naturality l E L ι W))

@[irreducible] private def scalarAdjunction (A : CoefficientExtensionSystems l E L ι W) :
    A.scalar.model.E ⊣ SheafOfModules.restrictScalars (scalarSystemMap l E L ι W) := by
  unfold scalarSystemMap
  exact A.scalar.ordinaryAdjunction

@[irreducible] private def rawScalarUnitSection
    (A : CoefficientExtensionSystems l E L ι W) (N : coefficientSequenceModules l E W)
    (n : ℕ) (U : W.ProEtᵒᵖ) (x : N.val.obj (op (n, U.unop))) :
    (A.scalar.model.E.obj N).val.obj (op (n, U.unop)) :=
  abstractUnitSection (scalarSystemMap l E L ι W) (scalarAdjunction l E L ι W A)
    N (op (n, U.unop)) x

end CoefficientExtensionAssociation
end WeilConjectures
