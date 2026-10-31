/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurCompletedReindexingData
import WeilConjectures.AlgebraicGeometry.CompletedOrdinaryComparisons

/-! # PurCompletedModuleReindexing

Source: Stacks Project and the extracted proof of
lem-pur-isomorphism-completed-reduction-reindexing.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
attribute [local irreducible] proEtaleRingModulePullback
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 2000] reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private def modulePullComp {U V W : Scheme.{t}} (h : U ⟶ V) (g : V ⟶ W) :
    proEtaleRingModulePullback (h ≫ g) (d.completedRing W) (d.completedRing U)
        (d.integralRingIso (h ≫ g)) ≅
      proEtaleRingModulePullback g (d.completedRing W) (d.completedRing V)
        (d.integralRingIso g) ⋙
      proEtaleRingModulePullback h (d.completedRing V) (d.completedRing U)
        (d.integralRingIso h) :=
  eqToIso (congrArg
    (proEtaleRingModulePullback (h ≫ g) (d.completedRing W) (d.completedRing U))
      (d.integralRingIso_comp h g)) ≪≫
    exchangeModuleComposition h g (d.completedRing W) (d.completedRing V)
      (d.completedRing U) (d.integralRingIso g) (d.integralRingIso h)

private def modulePullId (T : Scheme.{t}) :
    proEtaleRingModulePullback (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T)) ≅ 𝟭 _ :=
  (proEtaleRingModuleAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
    (d.integralRingIso (𝟙 T))).leftAdjointIdIso (d.modulePushId T)

private def moduleEquivalence {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] :
    reductionModules T (d.completedRing T) ≌ reductionModules T' (d.completedRing T') :=
  CategoryTheory.Equivalence.mk
    (proEtaleRingModulePullback u (d.completedRing T) (d.completedRing T')
      (d.integralRingIso u))
    (proEtaleRingModulePullback (inv u) (d.completedRing T') (d.completedRing T)
      (d.integralRingIso (inv u)))
    ((modulePullId d T).symm ≪≫
      eqToIso (congrArg (fun f : T ⟶ T ↦
        proEtaleRingModulePullback f (d.completedRing T) (d.completedRing T)
          (d.integralRingIso f)) (IsIso.inv_hom_id u).symm) ≪≫
      modulePullComp d (inv u) u)
    ((modulePullComp d u (inv u)).symm ≪≫
      eqToIso (congrArg (fun f : T' ⟶ T' ↦
        proEtaleRingModulePullback f (d.completedRing T') (d.completedRing T')
          (d.integralRingIso f)) (IsIso.hom_inv_id u)) ≪≫
      modulePullId d T')

/-- The tensor pullback is sectionwise reindexing on completed-ring modules, and
reverse pullback is its specified inverse.
Source: extracted proof, step 1; Stacks Tags 09A5, 00WX and 03D2.
(blueprint: lem-pur-completed-module-section-reindexing).
Proof: postcomposition with u and its inverse gives inverse covering-preserving
site equivalences. The comma-normalized inverse-image identification evaluates a
section by the inverse-image unit followed by the canonical comma restriction.
The completed coefficient isomorphism transports the action by its inverse; its
composition identity identifies reverse transport with the coefficient map for
inv u. The tensor-unit-normalized adjunction identifies this transport with the
published tensor pullback. Transporting the comma formula through that adjunction
gives the displayed section equation. The identity and composition equations for
completed coefficients give the unit and counit of the module equivalence; both
are natural in restrictions and module morphisms. Thus the inverse functor is the
published pullback along inv u, with the stated literal functor equalities. -/
theorem purCompletedModuleReindexing
    {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] :
  PurCompletedReindexingAtSections d u ∧
  PurCompletedReindexingAtModules d u := by
  let E := moduleEquivalence d u
  let P := proEtaleRingModulePullback u (d.completedRing T) (d.completedRing T')
    (d.integralRingIso u)
  have : P.IsEquivalence := E.isEquivalence_functor
  let adj := proEtaleRingModuleAdjunction u (d.completedRing T) (d.completedRing T')
    (d.integralRingIso u)
  let V := SheafOfModules.toSheaf (reductionModuleRing T (d.completedRing T))
  let V' := SheafOfModules.toSheaf (reductionModuleRing T' (d.completedRing T'))
  let S := isoSectionwiseInverseImage u AddCommGrpCat.{t + 1}
  let sadj : S ⊣ proEtaleSheafDirectImage u AddCommGrpCat.{t + 1} :=
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ u
      (inferInstance : WeaklyEtale u) trivial).sheafPushforwardContinuous _ _
  have : S.IsEquivalence :=
    (isoSectionwiseInverseImage_equivalence.{t, t + 2, t + 1, 0, 0}
      u AddCommGrpCat.{t + 1}).1
  have : (proEtaleSheafDirectImage u AddCommGrpCat.{t + 1}).IsEquivalence :=
    sadj.isEquivalence_right_of_isEquivalence_left
  have hu : IsIso adj.unit := by infer_instance
  have hc : IsIso sadj.counit := by infer_instance
  let e : V ⋙ S ≅ P ⋙ V' :=
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (asIso adj.unit) V) S ≪≫
      Functor.isoWhiskerLeft (P ⋙ V') (asIso sadj.counit)
  constructor
  · refine ⟨e.symm, ?_⟩
    intro M U x
    rfl
  · exact ⟨E, rfl, rfl⟩

end AlgebraicGeometry.Scheme
