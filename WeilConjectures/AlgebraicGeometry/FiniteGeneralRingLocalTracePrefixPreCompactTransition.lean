/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingLocalTracePrefixPreCompact
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingLocalTraceAffineHelper

/-! # Pre-compact frame-prefix transition

Source: general-ring smooth purity, proof (3), local frame calculation.
(blueprint: lem-sp-general-ring-integration-exponent-local-trace-prefix-precompact-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

set_option allowUnsafeReducibility true in
attribute [local irreducible] Etale.upperStar Etale.leftDerivedUpperStarComp
  Etale.rightDerivedLowerShriekOfCompactification
  VectorBundleZeroSection.π VectorBundleZeroSection.scheme
  Functor.leftDerivedFunctor _root_.DerivedCategory.singleFunctors
attribute [local implicit_reducible] Scheme.Modules Etale.FiniteSmoothPurity.line
  Etale.rightDerivedLowerShriek Etale.vectorIntegrationCoefficient
  Etale.vectorBundlePurityLower Etale.vectorBundlePurityCompactification
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

private lemma coefficient_transition
    {C D E : Type*} [Category C] [Category D] [Category E]
    (H H₁ H₂ : C ⥤ E) (U : C ⥤ D) (P : D ⥤ E)
    (c₁ : H ≅ H₁) (c₂ : H₁ ≅ H₂) (c₃ : H₂ ≅ U ⋙ P)
    {X Y : C} {B B' : D} {R R' : E}
    (a : X ⟶ Y) (v : B ⟶ B')
    (b : U.obj X ≅ B) (b' : U.obj Y ≅ B')
    (e : R ≅ P.obj B) (e' : R' ≅ P.obj B')
    (h : U.map a ≫ b'.hom = b.hom ≫ v) :
    H.map a ≫ ((c₁.app Y).hom ≫ (c₂.app Y).hom ≫ (c₃.app Y).hom ≫
        P.map b'.hom ≫ e'.inv) =
      ((c₁.app X).hom ≫ (c₂.app X).hom ≫ (c₃.app X).hom ≫
        P.map b.hom ≫ e.inv) ≫ (e.hom ≫ P.map v ≫ e'.inv) := by
  simp only [Iso.app_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [c₁.hom.naturality_assoc, c₂.hom.naturality_assoc, c₃.hom.naturality_assoc]
  simp only [Functor.comp_map, ← P.map_comp_assoc]
  rw [h]

private lemma exchange_transition
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (Q : C ⥤ E) (R : E ⥤ D) (η : L ⟶ Q ⋙ R)
    {X Y : C} {B B' : E} (a : X ⟶ Y)
    (b : Q.obj X ⟶ B) (b' : Q.obj Y ⟶ B') (v : B ⟶ B')
    (h : Q.map a ≫ b' = b ≫ v) :
    L.map a ≫ (η.app Y ≫ R.map b') = (η.app X ≫ R.map b) ≫ R.map v := by
  rw [← Category.assoc, η.naturality]
  simp only [Functor.comp_map, Category.assoc, ← R.map_comp]
  rw [h]

set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
-- The canonical derived-functor presentations require additional conversion work.
/-- Exchange and coefficient transport before the compact-support comparison.

This is the first independent stage of the local frame calculation: pullback of the
level power is moved through inverse-frame exchange and chart coefficient descent,
landing in the affine right tower.
Source: general-ring smooth purity, proof (3), local frame calculation.
Proof: expand the pre-compact prefix. The base-change exchange is a natural
transformation, so `V^*π_!π^*` of the level power moves past it and becomes
`p_!` of `chart^*π^*` of the level power. In the chart coefficient comparison the
inverse-image composition isomorphisms and the `eqToIso` of the Cartesian square are
natural, which turns `chart^*π^*` of the level power into `p^*V^*` of it; the hypothesis
`hlevel` replaces `V^*` of the level power followed by the base-coefficient comparison at
`N` by the comparison at `M` followed by the level power of `bV`; finally
`p^*` of that level power followed by the inverse descent at `N` is the inverse descent at
`M` followed by `finiteGeneralRingAffineTransition`, by the definition of the transition.
The hypotheses `hdiv` and `hbline` are not needed for the equation; they record the
canonical setting of the caller.
(blueprint: lem-sp-general-ring-integration-exponent-local-trace-prefix-precompact-transition). -/
theorem finiteGeneralRingLocalTracePrefix_preCompact_transition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hMpos : 0 < M) (hNpos : 0 < N) (hdiv : N ∣ M)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (M : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (b : Scheme.finiteEtaleTateLine S M A hM ≅
      Scheme.finiteEtaleTateLine S N A hN)
    (V : S.Opens)
    (bV : Scheme.finiteEtaleTateLine V.toScheme M A hM ≅
      Scheme.finiteEtaleTateLine V.toScheme N A hN)
    (tN : Etale.OrdinaryFiniteTwistTransport A N hN)
    (tM : Etale.OrdinaryFiniteTwistTransport A M hM)
    (eV : VectorBundleZeroSection.Trivialization S d F V)
    (hlevel : (Etale.ordinaryFinitePullback A V.ι).map
        (finiteGeneralRingLevelPower A M N hM hN S b d).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback A N hN tN V.ι hS' d).hom =
      (Etale.vectorIntegrationBaseCoefficientPullback A M hM tM V.ι hS d).hom ≫
        (finiteGeneralRingLevelPower A M N hM hN V.toScheme bV d).hom)
    (hbline : bV = (tM.line V.ι hS).symm ≪≫
      (Etale.upperStar (ModuleCat.{u + 1} A) V.ι).mapIso b ≪≫
      (tN.line V.ι hS')) :
    (Etale.ordinaryFinitePullback A V.ι).map
        ((Etale.vectorBundlePurityLower A S d F).map
          ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).map
            (finiteGeneralRingLevelPower A M N hM hN S b d).hom)) ≫
      finiteGeneralRingLocalTracePrefixPreCompact N hNpos A hN tN S hS' d F V eV =
      finiteGeneralRingLocalTracePrefixPreCompact M hMpos A hM tM S hS d F V eV ≫
        (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (affineTraceProjection V.toScheme d)).map
          (finiteGeneralRingAffineTransition A M N hM hN V.toScheme
            (by simpa using hS.map V.ι.appTop.hom)
            (by simpa using hS'.map V.ι.appTop.hom) bV tM tN d) := by
  let : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (Etale.vectorIntegration_geometry S d F).1
  let : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
    (Etale.vectorIntegration_geometry S d F).2.1
  let : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  let a := (finiteGeneralRingLevelPower A M N hM hN S b d).hom
  let j := Etale.vectorIntegrationChart S d F V eV
  let p := affineTraceProjection V.toScheme d
  have hc := coefficient_transition
    ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)) ⋙
      Etale.ordinaryFinitePullback A j) _ _
    (Etale.ordinaryFinitePullback A V.ι) (Etale.ordinaryFinitePullback A p)
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      j (VectorBundleZeroSection.π S d F)).symm
    (eqToIso (congrArg (Etale.ordinaryFinitePullback A)
      (Etale.vectorIntegrationChart_isPullback S d F V eV).w))
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p V.ι) a
    (finiteGeneralRingLevelPower A M N hM hN V.toScheme bV d).hom
    (Etale.vectorIntegrationBaseCoefficientPullback A M hM tM V.ι hS d)
    (Etale.vectorIntegrationBaseCoefficientPullback A N hN tN V.ι hS' d)
    (Etale.affineLinearCoefficientDescent A M hM tM V.toScheme
      (by simpa using hS.map V.ι.appTop.hom) d)
    (Etale.affineLinearCoefficientDescent A N hN tN V.toScheme
      (by simpa using hS'.map V.ι.appTop.hom) d) hlevel
  have he := exchange_transition
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π S d F) ⋙ Etale.ordinaryFinitePullback A V.ι)
    (Etale.ordinaryFinitePullback A j)
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) p)
    (Etale.rightDerivedLowerShriekBaseChangeMap A
      (Etale.vectorIntegrationChart_isPullback S d F V eV))
    ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).map a)
    (Etale.vectorIntegrationChartCoefficient A M hM tM S hS d F V eV).hom
    (Etale.vectorIntegrationChartCoefficient A N hN tN S hS' d F V eV).hom
    (finiteGeneralRingAffineTransition A M N hM hN V.toScheme
      (by simpa using hS.map V.ι.appTop.hom)
      (by simpa using hS'.map V.ι.appTop.hom) bV tM tN d)
    hc
  simpa only [finiteGeneralRingLocalTracePrefixPreCompact, Functor.comp_map,
    Category.assoc, a, j, p, Etale.vectorBundlePurityLower,
    Etale.vectorBundlePurityCompactification, Etale.rightDerivedLowerShriek,
    Etale.vectorIntegrationCoefficient, Etale.FiniteSmoothPurity.line] using he

end AlgebraicGeometry.ProEtale
