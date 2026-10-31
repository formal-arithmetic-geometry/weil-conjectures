/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingSupportSystemHom
public import WeilConjectures.SixFunctors.IntegralDualizingMappingTower
import WeilConjectures.SixFunctors.IntegralDualizingSupportReduction
import WeilConjectures.SixFunctors.PointIntegralReductionHomTower
import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus

/-! # Scalar adjunction for the compact-support quotient system -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

universe u₁ u₂ u₃ u₄ u₅ v₁ v₂ v₃ v₄ v₅

/-- Compose reduction before Hom with scalar adjunction on a full subcategory.
Keeping this categorical calculation abstract avoids expanding derived functors
when the kernel checks its associativity and full-subcategory identifications. -/
private theorem supportReductionHomIso
    {C₁ : Type u₁} [Category.{v₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂]
    {C₃ : Type u₃} [Category.{v₃} C₃]
    {C₄ : Type u₄} [Category.{v₄} C₄]
    {C₅ : Type u₅} [Category.{v₅} C₅]
    (P : ObjectProperty C₂) (F : C₁ ⥤ C₂) (R : C₂ ⥤ C₃)
    (U : C₁ ⥤ C₃) (H : C₃ᵒᵖ ⥤ C₄) (J : C₂ ⥤ C₅) (V : C₅ᵒᵖ ⥤ C₄)
    (hF : ∀ K, P (F.obj K)) (a : F ⋙ R ≅ U)
    (b : P.ι.op ⋙ R.op ⋙ H ≅ (P.ι ⋙ J).op ⋙ V) :
    Nonempty (U.op ⋙ H ≅ (F ⋙ J).op ⋙ V) := by
  let F' := P.lift F hF
  let c : U.op ⋙ H ≅ F'.op ⋙ (P.ι.op ⋙ R.op ⋙ H) :=
    Functor.isoWhiskerRight (NatIso.op a) H
  exact ⟨c ≪≫ Functor.isoWhiskerLeft F'.op b⟩

-- Match the displayed functors without unfolding their resolution constructions.
attribute [local irreducible] integralDualizingCompactTower integralDualizingLimit
  integralDualizingDerivedSections integralDualizingCoefficientHomTower
  coefPairingSections coefficientSequenceInternalHom sfIntegralConstructible

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Compare the dual of the quotient compact-support system with Hom from the
constant integral compact-support sections. There is no dualizing tower or
exceptional inverse image in this statement.

Source: prop-coef-integral-dualizing, second paragraph, last scalar-adjunction
comparison; integral compact-support reduction and point-section reduction.
(blueprint: lem-coef-integral-dualizing-support-system-hom-comparison).

Proof: choose a normalized reduction calculus B on the geometric base point.
The support-reduction theorem proves that the actual integral support functor F
has constructible values and compares F followed by B.reduction with quotient
system support, before applying Hom. Lift F to the full subcategory of integral
constructible point complexes. The point scalar-Hom theorem compares Hom from
the reduction of a point complex into the quotient unit with the coefficient
Hom tower of its actual integral sections. Pass the support comparison to
opposite functors and whisker by Hom into the quotient unit and sections.
Compose it with the point comparison whiskered by the lifted support functor.
The resulting section functor is definitionally integralDualizingCompactSections.
Both comparisons are natural isomorphisms before this composition; no family of
finite-level isomorphisms is lifted. Zero inputs and empty schemes are included. -/
theorem integralDualizing_support_system_hom_comparison
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S) :
    Nonempty (integralDualizingSupportSystemHom D l E X S G ≅
      (integralDualizingCompactSections l E D hl X).op ⋙
        integralDualizingCoefficientHomTower l E) := by
  obtain ⟨B, _⟩ := coefficientDerivedSystemEvaluationCalculus l E (Spec (.of D.k))
  obtain ⟨hF, ⟨a⟩⟩ := integralDualizing_support_reduction D l hl E X S G B
  obtain ⟨b⟩ := point_integral_reduction_hom_tower D l hl E B G.baseTensors
  exact supportReductionHomIso
    (sfIntegralConstructible l E (Spec (.of D.k))) _ B.reduction
    (integralDualizingSystemSupport D l E X S G) _
    (integralDualizingDerivedSections l E (Spec (.of D.k)))
    (integralDualizingCoefficientHomTower l E) hF a b

end WeilConjectures
