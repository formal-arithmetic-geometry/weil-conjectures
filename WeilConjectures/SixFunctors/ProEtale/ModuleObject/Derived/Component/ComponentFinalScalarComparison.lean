/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedProfiniteScalarCompatibility

/-! # Composition of the point-scalar comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (T : Scheme.{u}) [IsAffine T]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)]
  (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ T))

/-- The final scalar realization comparison for the component pullback.
Source: Hemo--Richarz--Scholbach, Remark 3.2 and Proposition 4.3(3)
(blueprint: lem-zl-component-final-scalar-comparison).

Proof: compose the profinite scalar realization comparison with the component realization
square and the canonical associator for derived restriction of scalars. Naturality of the
point factorization identifies the resulting composite with the point realization from the
underlying condensed scalar ring. -/
theorem component_final_scalar_comparison
    (a : Evaluation.A ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (profiniteCoefficient Λ (affineComponentSpace T)) (Over.mk (𝟙 (affineComponentSpace T))) ≅
      Evaluation.A (Scheme.ProEt.topology T) (condensedRingObj Λ T)
        (Scheme.ProEt.mk (𝟙 T)))
    (square : Nonempty (Evaluation.F
        ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T)) (Over.mk (𝟙 (affineComponentSpace T)))
        Over.mkIdTerminal ⋙ componentDerived Λ T α ≅
      RingDerivedScalarExtension.moduleDerivedExtension a.hom.hom ⋙
        Evaluation.F (Scheme.ProEt.topology T) (condensedRingObj Λ T)
          (Scheme.ProEt.mk (𝟙 T))
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T)))
    (point : Nonempty (profiniteScalarRealization Λ (affineComponentSpace T) ⋙
        componentDerived Λ T α ≅ condensedScalarRealization Λ T)) :
    Nonempty (condensedScalarRealization Λ T ≅
      RingDerivedScalarExtension.moduleDerivedExtension
          (a.hom.hom.comp (profiniteScalarMap Λ (affineComponentSpace T))) ⋙
        Evaluation.F (Scheme.ProEt.topology T) (condensedRingObj Λ T)
          (Scheme.ProEt.mk (𝟙 T))
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T)) := by
  obtain ⟨square⟩ := square
  obtain ⟨point⟩ := point
  obtain ⟨scalar⟩ := condensed_profinite_scalar_compatibility (Mon.mk Λ) (affineComponentSpace T)
  exact ⟨point.symm ≪≫ Functor.isoWhiskerRight scalar _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (RingDerivedScalarExtension.moduleDerivedExtension
        (profiniteScalarMap Λ (affineComponentSpace T))) square ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (RingDerivedScalarExtension.moduleDerivedExtensionComposition
        (profiniteScalarMap Λ (affineComponentSpace T)) a.hom.hom
        (a.hom.hom.comp (profiniteScalarMap Λ (affineComponentSpace T))) rfl) _⟩

end AlgebraicGeometry.ProEtale.CondensedRing
