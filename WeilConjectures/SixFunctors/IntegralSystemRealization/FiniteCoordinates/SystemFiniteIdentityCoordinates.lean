/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteRefinementMateCanonical
public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteAdjunctionCoordinates
import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteCompositorCoordinates
import WeilConjectures.SixFunctors.IntegralSystemRealization.SystemPushCompositionLaws
import all WeilConjectures.AlgebraicGeometry.AmbientProperOpen.OrdinaryAmbientProperOpenLaws

/-! # Identity normalization in fixed finite coordinates

Source: Stacks 03D8 and 07A7; the finite compositor calculation in
prop-sf-pf-coherence.proof.md.
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
  pullCoordinates pushCoordinates shriekCoordinates

set_option maxRecDepth 4096
set_option Elab.async false

private theorem identity_from_composition
    {A B : Type*} [Category A] [Category B] (P : A ⥤ A) (Q : B ⥤ B) (V : A ⥤ B)
    (e : P ≅ 𝟭 A) (f : Q ≅ 𝟭 B) (q : P ⋙ V ≅ V ⋙ Q)
    (hc : ∀ M, V.map (P.map (e.hom.app M)) ≫ q.hom.app M =
      q.hom.app (P.obj M) ≫ Q.map (q.hom.app M) ≫ Q.map (f.hom.app (V.obj M)))
    (M : A) :
    V.map (e.hom.app M) = q.hom.app M ≫ f.hom.app (V.obj M) := by
  let : Q.Faithful := Functor.Faithful.of_iso f.symm
  apply Q.map_injective
  apply (cancel_epi (q.hom.app (P.obj M))).1
  have hn := q.hom.naturality (e.hom.app M)
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  rw [Functor.map_comp, ← hn]
  exact hc M

set_option maxHeartbeats 1000000 in
-- The identity compositor calculation compares several derived coefficient presentations.
/-- The prescribed fixed direct coordinate preserves the canonical identity map.
Source: Stacks 03D8 and 07A7; the identity compositor in
prop-sf-pf-coherence.proof.md.
Proof: apply the finite compositor at the pair of identity maps. The system
identity-pair law and ordinary s_unital law identify its two compositors with
mapping the prescribed identity normalizations. Naturality of the direct
comparison and faithfulness of a functor isomorphic to the identity cancel the
remaining outer comparison. Transport this equality through the inverse
coefficient equivalence. This uses arbitrary inputs, including zero systems and
empty schemes, and imposes no condition on the coefficient characteristic.
(blueprint: lem-sf-system-finite-identity-coordinates). -/
theorem identity_coordinates (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (z : Realizations l E D o) (m : ℕ) (X : Spaces D) (M : System l E X.obj.left) :
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
    (fixedEvaluation l E m X.obj.left).map
        ((z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
          SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E)
            X.obj.left).hom.app M) =
      (fixedPush l E o m (𝟙 X.obj.left) M).hom ≫
        ((ordinary D A).sId X).hom.app (input l E m X.obj.left M) := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
  let R := sfIntrinsicDerivedEquivalence X.obj.left
    (Padic.coefficientExtensionRing l E (m + 1))
  let P := Operations.push l E o (𝟙 X.obj.left)
  let Q := ProperOpenPush A (𝟙 X.obj.left)
  let V := fixedEvaluation l E m X.obj.left
  let e : Operations.push l E o (𝟙 X.obj.left) ≅ 𝟭 (System l E X.obj.left) :=
    z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
    SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) X.obj.left
  let ef := (ordinary D A).sId X
  have hi : V.map (e.hom.app M) =
      (pushCoordinates l E o m (𝟙 X.obj.left)).hom.app M ≫ ef.hom.app (V.obj M) := by
    apply identity_from_composition P Q V e ef (pushCoordinates l E o m (𝟙 X.obj.left))
    intro N
    have h := compositor l E o z.compositors m (𝟙 X.obj.left) (𝟙 X.obj.left)
      (𝟙 X.obj.left) (Category.id_comp _) N
    dsimp only at h
    have hs := systemPushIdentityPair l E o z.compositors z.canonicalBridge X.obj.left N
    have hf := (s_unital (ordinary D A) (ordinary_pull_coherence D A) (𝟙 X)
      (input l E m X.obj.left N)).1
    have hf' :
        (conjugateIsoEquiv
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X.obj.left)).comp
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X.obj.left)))
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
            (𝟙 X.obj.left ≫ 𝟙 X.obj.left))
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 X.obj.left) (𝟙 X.obj.left))).hom.app
            (input l E m X.obj.left N) ≫
          (AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection.indexIso
            (ProperOpenPush A) (Category.id_comp (𝟙 X.obj.left))).hom.app
            (input l E m X.obj.left N) = Q.map (ef.hom.app (V.obj N)) := by
      exact hf
    rw [hf'] at h
    rw [show
        (z.compositors.pushComp l E (𝟙 X.obj.left) (𝟙 X.obj.left)).hom.app N ≫
          (eqToIso (congrArg (Operations.push l E o)
            (Category.id_comp (𝟙 X.obj.left)))).hom.app N = P.map (e.hom.app N) from
          hs] at h
    have hh := fixed_square R
      (push l E o m (𝟙 X.obj.left) (P.obj N)) (push l E o m (𝟙 X.obj.left) N)
      ((coefficientSequenceDerivedEvaluation l E X.obj.left m).map (P.map (e.hom.app N)))
      (Q.map (fixedPush l E o m (𝟙 X.obj.left) N).hom ≫ Q.map (ef.hom.app (V.obj N)))
      (by simpa only [A, R, P, Q, Functor.comp_obj, Functor.map_comp, Category.assoc] using h)
    simpa only [V, fixedEvaluation_map, fixedEvaluation_obj, fixedPush, pushCoordinates,
      NatIso.ofComponents_hom_app,
      A, R, P, Q, Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom,
      Iso.symm_hom, Iso.app_inv, Category.assoc] using hh
  change V.map (e.hom.app M) = (fixedPush l E o m (𝟙 X.obj.left) M).hom ≫
    ef.hom.app (V.obj M)
  simpa only [pushCoordinates, NatIso.ofComponents_hom_app] using hi

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
