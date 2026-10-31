/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ReconstructedPairRefinementData

/-! # Reconstructed RefinementTraceTransport

Source: blueprint sk-prop-sp-unique-adjoint, categorical proof, and
sk-thm-purity-transport Steps 2--4
(blueprint: lem-route-reconstructed-refinement-trace-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open WeilConjectures CompactSupportCondensedRealization PurIntegralSupportComparison
namespace WeilConjectures.ReconstructedPairRefinement
private theorem transport_trace
    {A B D : Type*} [Category A] [Category B] [Category D]
    (F G : A ⥤ B) (V : B ⥤ D) (F' G' : A ⥤ D)
    {M₁ M₂ : A} {L : B} (a : M₂ ⟶ M₁)
    (t₁ : F.obj M₁ ⟶ L) (t₂ : G.obj M₂ ⟶ L)
    (q : G.obj M₂ ≅ F.obj M₂) (q' : G'.obj M₂ ≅ F'.obj M₂)
    (bc₁ : V.obj (F.obj M₁) ≅ F'.obj M₁)
    (bc₂ : V.obj (F.obj M₂) ≅ F'.obj M₂)
    (bd : V.obj (G.obj M₂) ≅ G'.obj M₂)
    (h : F.map a ≫ t₁ = q.inv ≫ t₂)
    (hn : F'.map a ≫ bc₁.inv = bc₂.inv ≫ V.map (F.map a))
    (hs : V.map q.hom ≫ bc₂.hom = bd.hom ≫ q'.hom) :
    F'.map a ≫ bc₁.inv ≫ V.map t₁ = q'.inv ≫ bd.inv ≫ V.map t₂ := by
  have hi : bc₂.inv ≫ V.map q.inv = q'.inv ≫ bd.inv := by
    have he : V.mapIso q ≪≫ bc₂ = bd ≪≫ q' := Iso.ext hs
    exact congrArg Iso.inv he
  calc
    F'.map a ≫ bc₁.inv ≫ V.map t₁ = bc₂.inv ≫ V.map (F.map a ≫ t₁) := by
      rw [← Category.assoc, hn, Category.assoc, V.map_comp]
    _ = bc₂.inv ≫ V.map (q.inv ≫ t₂) := by rw [h]
    _ = q'.inv ≫ bd.inv ≫ V.map t₂ := by
      rw [V.map_comp, ← Category.assoc, hi, Category.assoc]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (C : ComparisonFamily l k)
  (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
  [f.IsOver (Spec (.of k))]

/-- The integral refinement counit equation transports through all three coefficient
realizations, for arbitrary integral objects and traces.
Source: blueprint sk-prop-sp-unique-adjoint categorical proof, Naturality;
sk-prop-sp-rational and sk-thm-sp-qbar; parent proof Steps 7--8.
Proof: apply the specified completed integral scalar extension to the input equality.
Naturality of its compact-support comparison and the coefficient refinement square
rewrite the image as the scalar equation. For rational realization apply the
rationalization/realization functor, use naturality of the specified realization
comparison, and invert its refinement square. For closure realization apply the
actual finite-valued closure scalar functor to the rational equality. Naturality
of the compact-support projection and condensedProjection_refinement identify the
inverse projection factors; all are invertible on bounded constructibles. Cancel
the inverse refinement and projection factors to obtain the closure equation.
All equalities are preserved by functors, so this works for arbitrary traces and
arbitrary integral morphisms; no representing-pair or theta hypothesis is needed.
(blueprint: lem-route-reconstructed-refinement-trace-transport). -/
theorem reconstructedRefinementTraceTransport
    {c d : Compactification f} (w : c.Refinement d)
    (M₁ M₂ : CondensedERealization.Integral l E X.scheme)
    (L : CondensedERealization.Integral l E Y.scheme) (a : M₂ ⟶ M₁)
    (t₁ : (support l E k C X Y f c).obj M₁ ⟶ L)
    (t₂ : (support l E k C X Y f d).obj M₂ ⟶ L)
    (h : (support l E k C X Y f c).map a ≫ t₁ =
      (comparison l E k C X Y f w).hom.app M₂ ≫ t₂) :
    (∀ (H : Type u) [NormedField H] [NormedAlgebra ℚ_[l] H]
      [FiniteDimensional ℚ_[l] H] (i : E →ₐ[ℚ_[l]] H),
      (support l H k C X Y f c).map ((integralScalar l E H i k X).map a) ≫
          scalarTrace l E k C X Y f H i c t₁ =
        (comparison l H k C X Y f w).hom.app ((integralScalar l E H i k X).obj M₂) ≫
          scalarTrace l E k C X Y f H i d t₂) ∧
    ((fieldSupport l E k C X Y f c).map ((realize l E k C X).map a) ≫
        fieldTrace l E k C X Y f c t₁ =
      (fieldComparison l E k C X Y f w).hom.app ((realize l E k C X).obj M₂) ≫
        fieldTrace l E k C X Y f d t₂) ∧
    (∀ b : E →ₐ[ℚ_[l]] PadicAlgCl l,
      (omegaSupport l k X Y f c).map
          (((realize l E k C X) ⋙ toOmega l E k b X).map a) ≫
        omegaTrace l E k C X Y f b c (fieldTrace l E k C X Y f c t₁) =
      (omegaComparison l k X Y f w).hom.app
          (((realize l E k C X) ⋙ toOmega l E k b X).obj M₂) ≫
        omegaTrace l E k C X Y f b d (fieldTrace l E k C X Y f d t₂)) := by
  have hfield : (fieldSupport l E k C X Y f c).map ((realize l E k C X).map a) ≫
      fieldTrace l E k C X Y f c t₁ =
    (fieldComparison l E k C X Y f w).hom.app ((realize l E k C X).obj M₂) ≫
      fieldTrace l E k C X Y f d t₂ := by
    let := (C.refinement E X Y f w).invertible
    let := (C.refinement E X Y f w).field_invertible
    have he := transport_trace
      (support l E k C X Y f c) (support l E k C X Y f d)
      (realize l E k C Y ⋙
        (boundedConstructible (CondensedERealization.Coefficient E Y.scheme)).ι)
      (realize l E k C X ⋙ fieldSupport l E k C X Y f c ⋙
        (boundedConstructible (CondensedERealization.Coefficient E Y.scheme)).ι)
      (realize l E k C X ⋙ fieldSupport l E k C X Y f d ⋙
        (boundedConstructible (CondensedERealization.Coefficient E Y.scheme)).ι)
      a t₁ t₂
      ((asIso (integralRefinement l E k (C.coefficient E) X Y f w)).app M₂)
      ((asIso (fieldRefinement (Profinite.continuousCoefficientRingObj E) w)).app
        ((realize l E k C X).obj M₂))
      (((C.coefficient E).atCompactification X Y f c).realization.app
        (ScalarLocalization.mk M₁))
      (((C.coefficient E).atCompactification X Y f c).realization.app
        (ScalarLocalization.mk M₂))
      (((C.coefficient E).atCompactification X Y f d).realization.app
        (ScalarLocalization.mk M₂))
      (by exact h)
      (by
        exact (((C.coefficient E).atCompactification X Y f c).realization.inv.naturality
          ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map
            a)))
      (by exact (C.refinement E X Y f w).realization M₂)
    apply ObjectProperty.hom_ext
    exact he
  refine ⟨?_, hfield, ?_⟩
  · intro H instH1 instH2 instH3 i
    let := (C.refinement E X Y f w).invertible
    let := (C.refinement H X Y f w).invertible
    have he := transport_trace
      (support l E k C X Y f c) (support l E k C X Y f d)
      (integralScalar l E H i k Y)
      (integralScalar l E H i k X ⋙ support l H k C X Y f c)
      (integralScalar l E H i k X ⋙ support l H k C X Y f d)
      a t₁ t₂
      ((asIso (integralRefinement l E k (C.coefficient E) X Y f w)).app M₂)
      ((asIso (integralRefinement l H k (C.coefficient H) X Y f w)).app
        ((integralScalar l E H i k X).obj M₂))
      ((C.finite E H i X Y f c).comparison.app M₁)
      ((C.finite E H i X Y f c).comparison.app M₂)
      ((C.finite E H i X Y f d).comparison.app M₂)
      (by exact h)
      (by exact ((C.finite E H i X Y f c).comparison.inv.naturality a))
      (by exact C.scalar_refinement E H i X Y f w M₂)
    exact he
  · intro b
    let N₁ := (realize l E k C X).obj M₁
    let N₂ := (realize l E k C X).obj M₂
    let := (C.refinement E X Y f w).field_invertible
    let := omegaRefinement_isIso l k X Y f w
    let := omegaProjection_isIso l E k b X Y f c N₁
    let := omegaProjection_isIso l E k b X Y f c N₂
    let := omegaProjection_isIso l E k b X Y f d N₂
    have he := transport_trace
      (fieldSupport l E k C X Y f c) (fieldSupport l E k C X Y f d)
      (toOmega l E k b Y ⋙ (boundedConstructible (padicAlgClRingObj Y.scheme l)).ι)
      (toOmega l E k b X ⋙ omegaSupport l k X Y f c ⋙
        (boundedConstructible (padicAlgClRingObj Y.scheme l)).ι)
      (toOmega l E k b X ⋙ omegaSupport l k X Y f d ⋙
        (boundedConstructible (padicAlgClRingObj Y.scheme l)).ι)
      ((realize l E k C X).map a)
      (fieldTrace l E k C X Y f c t₁) (fieldTrace l E k C X Y f d t₂)
      ((fieldComparison l E k C X Y f w).symm.app N₂)
      ((asIso (fieldRefinement (Profinite.padicAlgClRingObj.{u} l) w)).app
        ((toOmega l E k b X).obj N₂))
      (@asIso _ _ _ _ ((condensedProjection (omegaMap l E b) c).app N₁.obj)
        (omegaProjection_isIso l E k b X Y f c N₁))
      (@asIso _ _ _ _ ((condensedProjection (omegaMap l E b) c).app N₂.obj)
        (omegaProjection_isIso l E k b X Y f c N₂))
      (@asIso _ _ _ _ ((condensedProjection (omegaMap l E b) d).app N₂.obj)
        (omegaProjection_isIso l E k b X Y f d N₂))
      (by exact hfield)
      (by
        exact ((condensedProjection (omegaMap l E b) c).naturality_inv
          ((realize l E k C X).map a).hom).symm)
      (by
        exact condensedProjection_refinement (omegaMap l E b) w N₂
          (omegaScalar_preserves l E b X.scheme N₂))
    apply ObjectProperty.hom_ext
    exact he

end WeilConjectures.ReconstructedPairRefinement
