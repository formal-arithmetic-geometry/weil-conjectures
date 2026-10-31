/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteRefinementMateCanonical
public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteAdjunctionCoordinates
import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteAlphaCoordinates
import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteIdentityCoordinates
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import all WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientExactClopenComparison

/-! # Identity-left mate in fixed finite coordinates

Source: Stacks 00YV and 0F7B; the finite-evaluation step of
prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-system-finite-identity-left-mate-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.AmbientProperOpen
namespace WeilConjectures.IntegralSystemRealization.FiniteCoordinates

attribute [local implicit_reducible] TwoSquare integralCoefficientSheaf
  integralCoefficientCommRingSheaf
  scalarReductionTargetDerived coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientSheafTransition
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  RingHom.ulift
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  SemilinearProperOpen.derived coefficientSequenceHasDerived coefficientFiniteHasDerived ordinary

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] mateEquiv _root_.instCategoryDerivedCategory
  HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor Functor.leftDerivedFunctor CategoryTheory.constantSheaf
  AlgebraicGeometry.Scheme.residueField sfIntrinsicExtensionByZero
  sfIntrinsicDerivedEquivalence sfIntrinsicDerivedDirectImageComparison
  sfIntrinsicDerivedPullbackComp push shriek fixedPush fixedShriek
  SemilinearProperOpen.R SemilinearProperOpen.J properOpenMate
  Functor.ofOpSequence Functor.ofSequence
  CanonicalBridge.push CanonicalBridge.shriek CanonicalBridge.pull
  SemilinearProperOpen.sId properOpenAlpha
  derivedUpperStarLowerStarAdjunction
  AmbientClopen.realizationAlpha AmbientClopen.transportAlpha
  pullCoordinates pushCoordinates shriekCoordinates

set_option maxRecDepth 4096
set_option Elab.async false

private theorem inverse_word
    {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃)
    (d : X₀ ≅ X₄) (e : X₄ ≅ X₅) (f : X₅ ⟶ X₃)
    (h : a ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ f) :
    e.inv ≫ d.inv ≫ a = f ≫ c.inv ≫ b.inv := by
  apply (cancel_epi e.hom).1
  apply (cancel_epi d.hom).1
  apply (cancel_mono (b.hom ≫ c.hom)).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Iso.inv_hom_id, Category.comp_id, Category.id_comp] using h

set_option maxHeartbeats 1000000 in
-- Compare the prescribed adjunction presentations before applying the mate cube.
private theorem gamma_normalized (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (z : Realizations l E D o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : System l E U) :
    (z.properOpen.gamma k r p i h).app M =
      (mateEquiv (o.direct r).adj (o.direct p).adj (TwoSquare.mk _ _ _ _
        (AmbientClopen.realizationAlpha l E o z.canonicalBridge k r p i h))).app M := by
  have hh := AmbientClopen.realization_mate D l E k r p i h o z M
  simpa only [AmbientClopen.properMateFormula, mateEquiv_apply, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.comp_map, Functor.id_obj,
    Category.id_comp, Category.comp_id] using hh

private theorem mate_coordinates (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (z : Realizations l E D o) (m : ℕ)
    {U V Z : Scheme.{u}} (k : U ⟶ V) (p : V ⟶ Z) (i : U ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper p] (h : k ≫ p = (𝟙 U) ≫ i) (M : System l E U) :
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
    (fixedEvaluation l E m Z).map ((z.properOpen.gamma k (𝟙 U) p i h).app M) ≫
        (fixedPush l E o m p ((Operations.shriek l E o k).obj M)).hom ≫
        (ProperOpenPush A p).map (fixedShriek l E o m k M).hom =
      (fixedShriek l E o m i ((Operations.push l E o (𝟙 U)).obj M)).hom ≫
        (ProperOpenShriek A i).map (fixedPush l E o m (𝟙 U) M).hom ≫
        (properOpenMate A k (𝟙 U) p i h).app (input l E m U M) := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
  have hc := alpha_coordinates l E o z.canonicalBridge m k p i h
  have hp (B : System l E U) :
      (mateEquiv (o.direct (𝟙 U)).adj
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 U))
        (TwoSquare.mk _ _ _ _ (pullCoordinates l E o m (𝟙 U)).inv)).app B =
          (fixedPush l E o m (𝟙 U) B).hom := by
    have ht := congr_app (pullCoordinates_mate l E o m (𝟙 U)) B
    simpa only [pushCoordinates_hom_app] using ht
  have hq (B : System l E V) :
      (mateEquiv (o.direct p).adj
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
        (TwoSquare.mk _ _ _ _ (pullCoordinates l E o m p).inv)).app B =
          (fixedPush l E o m p B).hom := by
    have ht := congr_app (pullCoordinates_mate l E o m p) B
    simpa only [pushCoordinates_hom_app] using ht
  simp only [← shriekCoordinates_hom_app]
  refine exchangeMate_cube_all_normalized
    (o.direct (𝟙 U)).adj (o.direct p).adj
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 U))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (fixedEvaluation l E m U) (fixedEvaluation l E m U)
    (fixedEvaluation l E m Z) (fixedEvaluation l E m V)
    (pullCoordinates l E o m (𝟙 U)) (shriekCoordinates l E o m i)
    (shriekCoordinates l E o m k) (pullCoordinates l E o m p)
    (AmbientClopen.realizationAlpha l E o z.canonicalBridge k (𝟙 U) p i h)
    (properOpenAlpha A k (𝟙 U) p i h) ?_ M
    (fixedPush l E o m (𝟙 U) M).hom
    (fixedPush l E o m p ((Operations.shriek l E o k).obj M)).hom
    ((z.properOpen.gamma k (𝟙 U) p i h).app M)
    ((properOpenMate A k (𝟙 U) p i h).app (input l E m U M))
    (gamma_normalized l E D o z k (𝟙 U) p i h M).symm
    ?_ (hp M) (hq ((Operations.shriek l E o k).obj M))
  · intro N
    have ht := inverse_word _
      ((shriekCoordinates l E o m k).app ((pull l E (𝟙 U)).obj N))
      ((ProperOpenShriek A k).mapIso ((pullCoordinates l E o m (𝟙 U)).app N))
      ((pullCoordinates l E o m p).app ((Operations.shriek l E o i).obj N))
      ((ProperOpenPull A p).mapIso ((shriekCoordinates l E o m i).app N))
      _ (hc N)
    simpa only [Iso.app_inv, Functor.mapIso_inv] using ht
  · unfold properOpenMate
    rfl

set_option maxHeartbeats 1000000 in
-- The assembly compares several presentations of the same derived coefficient category.
/-- Fixed evaluation of an identity-left mate, including identity normalization.

Source: Stacks 00YV, 03D8, and 0F7B; the finite evaluated proper/open transport
in prop-sf-pf-coherence.proof.md.
Proof: take proper direct-image mates of the exact finite pull/open square,
using the normalized exchange-mate cube and the prescribed pull comparison's
mate equation. The bridge-transported semilinear mate is the given gamma.
Precompose with the canonical system identity normalization, use naturality of
the open comparison, and replace the evaluated identity by the inverse ordinary
identity normalization, as proved from the finite compositor. The resulting word
is the fixed mate word. The same cancellation applies to zero inputs, empty
opens, and identity maps.
(blueprint: lem-sf-system-finite-identity-left-mate-coordinates). -/
theorem identityLeftMateCoordinates (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (z : Realizations l E D o) (m : ℕ) (X : Spaces D)
    {V Z : Scheme.{u}} (k : X.obj.left ⟶ V) (p : V ⟶ Z) (i : X.obj.left ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper p] (h : k ≫ p = (𝟙 X.obj.left) ≫ i) (M : System l E X.obj.left) :
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
    let η : Operations.push l E o (𝟙 X.obj.left) ≅ 𝟭 (System l E X.obj.left) :=
      z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
        SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) X.obj.left
    (fixedEvaluation l E m Z).map
        ((Operations.shriek l E o i).map (η.inv.app M)) ≫
      (fixedEvaluation l E m Z).map
        ((z.properOpen.gamma k (𝟙 X.obj.left) p i h).app M) ≫
      (fixedPush l E o m p ((Operations.shriek l E o k).obj M)).hom ≫
      (ProperOpenPush A p).map (fixedShriek l E o m k M).hom =
    (fixedShriek l E o m i M).hom ≫
      (ProperOpenShriek A i).map
        (((ordinary D A).sId X).inv.app (input l E m X.obj.left M)) ≫
      (properOpenMate A k (𝟙 X.obj.left) p i h).app (input l E m X.obj.left M) := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
  let η : Operations.push l E o (𝟙 X.obj.left) ≅ 𝟭 (System l E X.obj.left) :=
    z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
    SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) X.obj.left
  let V := fixedEvaluation l E m X.obj.left
  let Ji := ProperOpenShriek A i
  let sid := (ordinary D A).sId X
  have hid : V.map (η.inv.app M) ≫ (fixedPush l E o m (𝟙 X.obj.left) M).hom =
      sid.inv.app (input l E m X.obj.left M) := by
    apply (cancel_mono (sid.hom.app (input l E m X.obj.left M))).1
    rw [Category.assoc, ← identity_coordinates l E D o z m X M, ← V.map_comp]
    change V.map (η.inv.app M ≫ η.hom.app M) =
      sid.inv.app (input l E m X.obj.left M) ≫ sid.hom.app (input l E m X.obj.left M)
    rw [Iso.inv_hom_id_app, V.map_id, Iso.inv_hom_id_app]
    rfl
  have hmate := mate_coordinates l E D o z m k p i
    h M
  dsimp only at hmate
  have hn := (shriekCoordinates l E o m i).hom.naturality (η.inv.app M)
  simp only [shriekCoordinates, NatIso.ofComponents_hom_app, Functor.comp_map] at hn
  have hfixed :
      (fixedEvaluation l E m Z).map
          ((Operations.shriek l E o i).map (η.inv.app M)) ≫
        (fixedEvaluation l E m Z).map
          ((z.properOpen.gamma k (𝟙 X.obj.left) p i
            h).app M) ≫
        (fixedPush l E o m p ((Operations.shriek l E o k).obj M)).hom ≫
        (ProperOpenPush A p).map (fixedShriek l E o m k M).hom =
      (fixedShriek l E o m i M).hom ≫ Ji.map (sid.inv.app (input l E m X.obj.left M)) ≫
        (properOpenMate A k (𝟙 X.obj.left) p i
          h).app (input l E m X.obj.left M) := by
    have h₁ := congrArg
      (fun t ↦ (fixedEvaluation l E m Z).map
        ((Operations.shriek l E o i).map (η.inv.app M)) ≫ t) hmate
    refine h₁.trans ?_
    have h₂ := congrArg
      (fun t ↦ t ≫ Ji.map (fixedPush l E o m (𝟙 X.obj.left) M).hom ≫
        (properOpenMate A k (𝟙 X.obj.left) p i
          h).app (input l E m X.obj.left M)) hn
    simp only [Functor.comp_obj, Functor.id_obj, Category.assoc] at h₂
    have h₃ := congrArg
        (fun t ↦ (fixedShriek l E o m i M).hom ≫ Ji.map t ≫
          (properOpenMate A k (𝟙 X.obj.left) p i
            h).app (input l E m X.obj.left M)) hid
    simp only [Functor.map_comp, Category.assoc] at h₃
    simpa only [A, Ji, fixedEvaluation_map, Functor.comp_map, Functor.comp_obj,
      Functor.id_obj, Category.assoc] using h₂.trans h₃
  exact hfixed

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
