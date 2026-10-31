/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemCanonicalBridge
import all WeilConjectures.AlgebraicGeometry.IntegralSupportNormalizationData

/-! # Section-normalized identity direct image

Source: Stacks Tag 03D8; current blueprint sk-thm-purity-transport, Steps 2--3,
identity proper factor of compact-support realization
(blueprint: def-pur-compact-support-realization-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures IntegralSystemRealization

namespace WeilConjectures.CompactSupportRealizationFactorization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical coefficient map followed by inverse identity-base-change restriction
is the identity ring map. Source: Stacks Tag 03D8, blueprint transport Steps 2--3
(blueprint: def-pur-compact-support-realization-identity).
Proof: compose with every positive quotient projection. The defining completed map
becomes the constant-section direct-image map. Identity base change restricts this
map to identity on each constant section. Sheafification gives equality at each
quotient, and the completed limit projections are jointly monic. -/
theorem identityCoefficient (W : Scheme.{u}) :
    let B := (sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((PurCompactSupport.completed l E).ring W)
    let φ : B ⟶ ((proEtaleBaseChange (𝟙 W)).sheafPushforwardContinuous
        RingCat.{u + 1} (ProEt.topology W) (ProEt.topology W)).obj B :=
      ⟨Functor.whiskerRight
        (proEtaleRingDirectImageMap (𝟙 W) ((PurCompactSupport.completed l E).ring W)
          ((PurCompactSupport.completed l E).ring W)
          ((PurCompactSupport.completed l E).pull (𝟙 W))).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    φ ≫ (Functor.sheafPushforwardContinuousNatTrans
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ W).inv _ _ _).app B = 𝟙 B := by
  dsimp only
  rw [IntegralSupportNormalization.ringDirectImageId]
  ext U x
  change (((completedIntegralCommRingSheafUnrestricted l E W).obj.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ W).hom.app U.unop).op ≫
    (completedIntegralCommRingSheafUnrestricted l E W).obj.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ W).inv.app U.unop).op) x) = x
  rw [← Functor.map_comp, ← CategoryTheory.op_comp, Iso.inv_hom_id_app,
    CategoryTheory.op_id, (completedIntegralCommRingSheafUnrestricted l E W).obj.map_id]
  rfl

/-- The ordinary identity direct-image unitor is explicitly inverse base-change
restriction on sections. Source: Stacks Tag 03D8, blueprint transport Steps 2--3
(blueprint: def-pur-compact-support-realization-identity). -/
def ordinaryPushId (W : Scheme.{u}) :
    proEtaleRingModuleDirectImage (𝟙 W) ((PurCompactSupport.completed l E).ring W)
      ((PurCompactSupport.completed l E).ring W)
      ((PurCompactSupport.completed l E).pull (𝟙 W)) ≅ 𝟭 _ :=
  letI : (𝟭 (MorphismProperty.Over @WeaklyEtale ⊤ W)).IsContinuous
      (ProEt.topology W) (ProEt.topology W) := Functor.isContinuous_id _
  let B := (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((PurCompactSupport.completed l E).ring W)
  let φ : B ⟶ ((proEtaleBaseChange (𝟙 W)).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology W) (ProEt.topology W)).obj B :=
    ⟨Functor.whiskerRight
      (proEtaleRingDirectImageMap (𝟙 W) ((PurCompactSupport.completed l E).ring W)
        ((PurCompactSupport.completed l E).ring W)
        ((PurCompactSupport.completed l E).pull (𝟙 W))).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  SheafOfModules.pushforwardCongr₂ (φ := φ)
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ W).symm
      (identityCoefficient l E W) ≪≫
    SheafOfModules.pushforwardId _

/-- Derive the section-normalized direct-image unitor and then remove the derived
identity localization factors. Source: Stacks Tag 03D8, blueprint transport Steps 2--3
(blueprint: def-pur-compact-support-realization-identity). -/
def integralPushId (W : Scheme.{u}) : ringedPush l E (𝟙 W) ≅ 𝟭 _ :=
  Functor.rightDerivedFunctorNatIso (ordinaryPushId l E W) ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

end WeilConjectures.CompactSupportRealizationFactorization
