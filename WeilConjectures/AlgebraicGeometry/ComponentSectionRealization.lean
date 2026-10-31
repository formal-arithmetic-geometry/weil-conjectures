/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedLisseEvaluationModel
import WeilConjectures.AlgebraicGeometry.ComponentInverseFullyFaithful
import WeilConjectures.AlgebraicGeometry.ComponentSectionScalarNormalization
import WeilConjectures.AlgebraicGeometry.ComponentSectionDerivedSquare
import WeilConjectures.AlgebraicGeometry.ComponentSectionRealizationPoint

/-! # Normalized section-ring realization square for component pullback

Source: Hemo--Richarz--Scholbach, Remark 3.2 and Proposition 4.3(3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
  (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)]

/-- The section-ring square and point realization square, with constant scalars fixed.
Source: Hemo--Richarz--Scholbach, (3.1)--(3.2), Remark 3.2, Proposition 4.3(3)
(blueprint: lem-zl-component-section-realization).

Proof: identify each terminal section ring with the convolution ring of morphisms
from the tensor unit. Apply the specified monoidal inverse image and the coefficient
isomorphism α to construct a ring map. Full faithfulness of component inverse image
makes this map bijective. Construct a from this bijection. For a point scalar r,
represent r by its adjunct map from the constant abelian unit. Naturality of β and its
monoidal unit equation give exactly the section defining affineScalarSection.
For the first functor isomorphism take a flat-term K-flat complex over the profinite
section ring. Inverse image preserves constants and ordinary tensor, so the coefficient
identification and the balanced maps b tensor (a tensor p) to ba tensor p identify the
two realizations. The inverse sends b tensor p to b tensor (1 tensor p). Balancing makes
them inverse chain maps natural in the complex. K-flat preservation and descent give
the isomorphism on the whole unbounded derived category. For the point realization,
lift β to ordinary module objects and cancel the
coefficient transport using α. Derive this ordinary natural isomorphism termwise;
functor associators give the second isomorphism. Empty schemes and zero rings reduce
to zero modules;
no connectedness, boundedness, or nonzero-ring hypothesis is used. -/
theorem component_section_realization
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ.X T))
    (β : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
      (affineComponentSpace T) ⋙ componentInverse T ≅ upperStarFromPoint T)
    (hβ : NatTrans.IsMonoidal β.hom) (hα : α.hom.hom = β.hom.app Λ.X) :
    ∃ a : Evaluation.A ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ.X (affineComponentSpace T))
        (Over.mk (𝟙 (affineComponentSpace T))) ≅
        Evaluation.A (Scheme.ProEt.topology T) (condensedRingObj Λ.X T)
          (Scheme.ProEt.mk (𝟙 T)),
      (∀ r : condensedScalarRing Λ.X,
        a.hom.hom (profiniteScalarMap Λ.X (affineComponentSpace T) r) =
          affineScalarSection Λ.X T r) ∧
      Nonempty (Evaluation.F ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
          (profiniteCoefficient Λ.X (affineComponentSpace T))
          (Over.mk (𝟙 (affineComponentSpace T))) Over.mkIdTerminal ⋙ componentDerived Λ.X T α ≅
        RingDerivedScalarExtension.moduleDerivedExtension a.hom.hom ⋙
          Evaluation.F (Scheme.ProEt.topology T) (condensedRingObj Λ.X T)
            (Scheme.ProEt.mk (𝟙 T))
            (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T)) ∧
      Nonempty (profiniteScalarRealization Λ.X (affineComponentSpace T) ⋙
        componentDerived Λ.X T α ≅ condensedScalarRealization Λ.X T) := by
  obtain ⟨h⟩ := component_inverse_fully_faithful T
  let a := (RingEquiv.ofBijective (componentSectionMap Λ T α)
    (componentSectionMap_bijective Λ T α h)).toCommRingCatIso
  refine ⟨a, ?_, ?_, component_section_realization_point Λ T α β hβ hα⟩
  · exact component_section_scalar_normalization Λ T α β hβ hα
  · exact component_section_derived_square Λ T α

end AlgebraicGeometry.ProEtale.CondensedRing
