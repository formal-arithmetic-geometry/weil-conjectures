/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SmoothPurity.Rational.RationalPullbackStageCoherence
import WeilConjectures.SmoothPurity.Rational.RationalPullbackScalarRightMate
import all Mathlib.Logic.Small.Defs

/-! # Coefficient-change mates before common-stage descent

Coherent coefficient pullback comparisons, and invertibility of the induced direct-image mates
for supplied right adjoints.

## Implementation details

For `E ⊆ F`, `𝒪_F` is finite free over `𝒪_E`. Scalar extension `T` is left adjoint to
restriction `Res`, and after rationalization the trace form is nondegenerate, so `Res` is also
left adjoint to `T`. Pullback commutes with `Res`, and the mate `T R_E ⟶ R_F T` of the inverse
pullback comparison is conjugate to the invertible comparison `Res L_F ⟶ L_E Res` under the
composite adjunctions, hence invertible. Only the supplied right adjoints are used, so the
argument applies to arbitrary scheme maps; the counit equation is obtained by consumers from
`mateEquiv_counit`.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.7.2, Proposition 6.8.14(2),
  Remark 6.8.15.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] rationalDerivedPullback sfRationalScalarExtension
  rationalPullbackScalarComparison HasDerivedCategory.standard
  ObjectProperty.FullSubcategory.category Padic.coefficientExtensionIntegers
  ScalarLocalization.category ScalarLocalization.composition

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition
  GeneralAlgebraicallyClosedCoefficients.stageSystem

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

private theorem rightMate_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (hG : G = G') (hH : H = H') (e : L₁ ⋙ H' ≅ G' ⋙ L₂)
    (hi : IsIso (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ e.inv))) :
    IsIso (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _
      (Functor.isoWhiskerLeft L₁ (eqToIso hH) ≪≫ e ≪≫
        Functor.isoWhiskerRight (eqToIso hG).symm L₂).inv)) := by
  subst G' H'
  simpa only [eqToIso_refl, Functor.isoWhiskerLeft_refl, Iso.refl_symm,
    Functor.isoWhiskerRight_refl, Iso.refl_trans, Iso.trans_refl] using hi

private theorem rightMate_transport_stage
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : ∀ E : Index l Ω,
      sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X ⥤
        sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (a : ∀ E, rationalDerivedPullback l (Coefficient.{u} l Ω E) f ⊣ R E)
    {E F : Index l Ω} (h : E ≤ F)
    (hY : (stageSystem l Ω Y).T h =
      GeneralAlgebraicallyClosedCoefficients.transition l Ω Y E F h)
    (hX : (stageSystem l Ω X).T h =
      GeneralAlgebraicallyClosedCoefficients.transition l Ω X E F h)
    (hi : IsIso (mateEquiv (a E) (a F) (TwoSquare.mk _ _ _ _
      (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω F)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E F h) f).inv))) :
    IsIso (mateEquiv (a E) (a F) (TwoSquare.mk _ _ _ _
      (rationalPullbackStageComparison l Ω f h).inv)) := by
  unfold rationalPullbackStageComparison
  exact rightMate_transport
    (L₁ := rationalDerivedPullback l (Coefficient.{u} l Ω E) f) (R₁ := R E)
    (L₂ := rationalDerivedPullback l (Coefficient.{u} l Ω F) f) (R₂ := R F)
    (G := (stageSystem l Ω Y).T h)
    (G' := GeneralAlgebraicallyClosedCoefficients.transition l Ω Y E F h)
    (H := (stageSystem l Ω X).T h)
    (H' := GeneralAlgebraicallyClosedCoefficients.transition l Ω X E F h)
    (a E) (a F) hY hX
    (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω F)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E F h) f) hi

-- The transported coefficient structures are unfolded with `respectTransparency false`.
/-- Coherent coefficient pullback comparisons and invertible direct-image mates. -/
theorem sfRationalDirectImageCoefficientCompatibility
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! L : (stageSystem l Ω Y).Morphism
        (stageSystem l Ω X),
      L.Φ = (fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f) ∧
      (∀ (E F : Index l Ω) (h : E ≤ F)
        (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
          Y),
        HEq ((L.β h).app K)
          (commonStagePullbackComparison l Ω f ⟨E, K⟩ F h)) ∧
      ∀ (R : ∀ E : Index l Ω,
        sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
            X ⥤
          sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
            Y)
        (a : ∀ E, L.Φ E ⊣ R E),
        ∀ {E F : Index l Ω} (h : E ≤ F),
          IsIso ((mateEquiv (a E) (a F) (TwoSquare.mk _ _ _ _ (L.β h).inv))) := by
  obtain ⟨b, hb, hcoh⟩ := commonStagePullback_comparison_data l Ω f
  let L : (stageSystem l Ω Y).Morphism (stageSystem l Ω X) :=
    { Φ := fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f
      β := b
      coh := hcoh }
  have hn : ∀ (E F : Index l Ω) (h : E ≤ F)
      (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      HEq ((L.β h).app K) (commonStagePullbackComparison l Ω f ⟨E, K⟩ F h) := by
    intro E F h K
    apply heq_of_eq
    apply Iso.ext
    exact eq_of_heq (hb h K).1
  refine ⟨L, ⟨rfl, hn, ?_⟩, ?_⟩
  · intro R a E F h
    dsimp only [L] at a ⊢
    have hbIso : b h = rationalPullbackStageComparison l Ω f h := by
      apply Iso.ext
      apply NatTrans.ext
      funext K
      exact eq_of_heq (hb h K).1
    rw [hbIso]
    let E' := Coefficient.{u} l Ω E
    let F' := Coefficient.{u} l Ω F
    let := (inferInstance : Field E')
    let := (inferInstance : Algebra (ℚ_[l]) E')
    let := (inferInstance : FiniteDimensional (ℚ_[l]) E')
    let := (inferInstance : Field F')
    let := (inferInstance : Algebra (ℚ_[l]) F')
    let := (inferInstance : FiniteDimensional (ℚ_[l]) F')
    let ι := AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E F h
    have hY := (stageSystem_existsUnique l Ω Y).exists.choose_spec.1 E F h
    have hX := (stageSystem_existsUnique l Ω X).exists.choose_spec.1 E F h
    let hi := rationalPullbackScalar_rightMate_isIso l E' F' ι f (R E) (R F) (a E) (a F)
    exact rightMate_transport_stage l Ω f R a h hY hX hi
  · rintro ⟨Φ, β, coh⟩ ⟨hΦ, hβ, _⟩
    dsimp only at hΦ
    cases hΦ
    have he : @β = @L.β := by
      funext E F h
      apply Iso.ext
      apply NatTrans.ext
      funext K
      have h := (hβ E F h K).trans (hn E F h K).symm
      exact congrArg Iso.hom (eq_of_heq h)
    cases he
    rfl

end WeilConjectures
