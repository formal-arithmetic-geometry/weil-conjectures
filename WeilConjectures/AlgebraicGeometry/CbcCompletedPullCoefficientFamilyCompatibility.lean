/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CbcCompletedPullCoefficientFamilyCore

/-! # Strict completed-pullback coefficient family argument

Source: current blueprint, coefficient coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

structure CbcCompletedPullCoefficientFamilyCompatibility (l : ℕ) (Ω : Type w)
    [Fact l.Prime] [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    {g : Y ⟶ X} (C : CbcCompletedPullCoefficientFamilyCore l Ω g) where
  comparison : ∀ {E F} (h : E ≤ F),
    pbcEmbeddingAmbientTensor l (pbcFiniteField l Ω E) (pbcFiniteField l Ω F)
        (pbcFiniteFieldInclusion l Ω h) X ⋙
        (pbcStageDatum l Ω F).completedPull g ≅
      (pbcStageDatum l Ω E).completedPull g ⋙
        pbcEmbeddingAmbientTensor l (pbcFiniteField l Ω E) (pbcFiniteField l Ω F)
          (pbcFiniteFieldInclusion l Ω h) Y
  completionUnit : ∀ {E F} (h : E ≤ F)
    (K : pbcAmbientStage l Ω X E),
    (pbcStageDatum l Ω F).ordinaryToCompleted g
        ((pbcEmbeddingAmbientTensor l (pbcFiniteField l Ω E)
          (pbcFiniteField l Ω F) (pbcFiniteFieldInclusion l Ω h) X).obj K) ≫
      (comparison h).hom.app K =
    (Functor.isoWhiskerLeft _
        (cbcDatumOrdinaryTransport (pbcStageDatum l Ω F) g).symm ≪≫
      pbcScalarOrdinaryPullIso l (pbcFiniteField l Ω E)
        (pbcFiniteField l Ω F) (pbcFiniteFieldInclusion l Ω h) g ≪≫
      Functor.isoWhiskerRight
        (cbcDatumOrdinaryTransport (pbcStageDatum l Ω E) g) _).hom.app K ≫
      (pbcEmbeddingAmbientTensor l (pbcFiniteField l Ω E)
        (pbcFiniteField l Ω F) (pbcFiniteFieldInclusion l Ω h) Y).map
        ((pbcStageDatum l Ω E).ordinaryToCompleted g K)
  beta : ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (K : pbcIntegralStage l Ω X E),
    ∃ (hs : PbcIsBoundedConstructibleComplete Y (pbcStageDatum l Ω F)
        (((pbcStageDatum l Ω F).completedPull g).obj
          ((pbcEmbeddingAmbientTensor l (pbcFiniteField l Ω E)
            (pbcFiniteField l Ω F) (pbcFiniteFieldInclusion l Ω h) X).obj K.obj)))
      (ht : PbcIsBoundedConstructibleComplete Y (pbcStageDatum l Ω F)
        ((pbcEmbeddingAmbientTensor l (pbcFiniteField l Ω E)
          (pbcFiniteField l Ω F) (pbcFiniteFieldInclusion l Ω h) Y).obj
            (((pbcStageDatum l Ω E).completedPull g).obj K.obj))),
      HEq
        ((eqToIso (C.localization F)).inv.app
            ((pbcIntegralScalarExtension l Ω X _ _ h).obj K) ≫
          (C.family.base.Φ F).map
            ((pbcScalarIntegralComparison l Ω X _ _ h).inv.app K) ≫
          (C.family.base.β h).inv.app ((pbcStageLocalization l Ω X E).obj K) ≫
          ((pbcScalarSystem l Ω Y _ _).T h).map
            ((eqToIso (C.localization E)).hom.app K) ≫
          (pbcScalarIntegralComparison l Ω Y _ _ h).hom.app
            ((pbcConditionalIntegral (pbcStageDatum l Ω E)
              ((pbcStageDatum l Ω E).completedPull g) (C.preserves E)).obj K))
        ((pbcStageLocalization l Ω Y F).map
          (ObjectProperty.homMk (X := ⟨_, hs⟩) (Y := ⟨_, ht⟩)
            ((comparison h).hom.app K.obj)))
  unit : ∀ E : Padic.FiniteCoefficientFields l Ω,
    HEq (C.family.base.β (le_refl E)) (Iso.refl (C.family.base.Φ E))

/-- Strict completed-pullback family scalar compatibility.

Source: current blueprint, coefficient coherence.
(blueprint: lem-cbc-normalized-pull-family-compatibility)

Proof: For E≤F let e_E and e_F be the core ambient strict-to-reflector isomorphisms. Define the
comparison as C_X e_F followed by pbcScalarCompletedPullIso followed by e_E inverse whiskered by
C_Y. The equation scalarCompletedPull_unit and the two core ambientUnit equations imply the
required completion-unit equation after cancelling e_E and using functoriality. The
integralTransport_hom equations identify the corresponding integral restricted maps with this
ambient composite; the inverse equations follow by inverse cancellation. Rebase normalized
pbcAmbientScalarExtension to pbcEmbeddingAmbientTensor via pbcStageCoefficientMap_eq. Apply the
core reflectorBeta specification and pbcScalarCompletedPull_rational.exists.choose_spec on an
integral representative. Use core transportedBeta and rationalTransport_hom to expand the
conjugated inverse beta. Naturality of rational transport at the source scalar comparison moves
its inverse component to the left. Naturality of the target scalar/integral comparison moves the
localized integral transport component to the right. The middle term is exactly the reflector
beta expression. Functoriality of localization combines the three integral maps, which are the
restriction of the constructed ambient comparison. Full-subcategory object extensionality and
HEq transport endpoints between the two scalar-extension presentations. At repeated stages
pbcScalarSystem_units makes both scalar functors identities and both associators unitors. The
core family coherence equation then makes each beta component an invertible idempotent; cancel
it to obtain identity. Iso.ext and natural-transformation extensionality prove the final unit
equation.
-/
theorem cbcCompletedPullCoefficientFamilyCompatibility_exists
    (l : ℕ) (Ω : Type w)
    [Fact l.Prime] [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    {g : Y ⟶ X} (C : CbcCompletedPullCoefficientFamilyCore l Ω g) :
    Nonempty (CbcCompletedPullCoefficientFamilyCompatibility l Ω C) := by
  sorry

end AlgebraicGeometry.Scheme
