/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimitSupport

/-! # Assembling strict scalar comparisons from their normalized finite components
Source: blueprint direct-image proof, paragraph (2).
(blueprint: lem-sp-compactification-ordinary-scalar-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The normalized component of the strict open scalar comparison, before checking
horizontal naturality. Source: Stacks 03DI; blueprint direct-image paragraph (2).
(blueprint: lem-sp-compactification-ordinary-scalar-assembly). -/
def openLevelScalar (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (h : ScalarSquares l E)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (DX : SpCoefficientTowersAbelian l E X) (DZ : SpCoefficientTowersAbelian l E Z)
    (vX : Evaluation l E b X DX) (vZ : Evaluation l E b Z DZ) (n : ℕ) :
    (forgetting l E X DX ⋙ fixedOpenOrd l E j) ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (scalarReductionSource l E Z)).obj (op n) ≅
      (ordinaryTowerOpen l E b o j ⋙ forgetting l E Z DZ) ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (scalarReductionSource l E Z)).obj (op n) :=
  Functor.isoWhiskerLeft (spCoefficientEvaluation l E X DX.equivalence n)
      (ordinaryOpenScalar l E b h j n) ≪≫
    Functor.isoWhiskerRight
      (ordinaryOpenEvaluation l E b o j DX DZ vX vZ n).symm
      (spCompletedEllRestriction l E Z n)

/-- The normalized component of the strict direct-image scalar comparison.
Source: Stacks 03D7; blueprint direct-image paragraph (2).
(blueprint: lem-sp-compactification-ordinary-scalar-assembly). -/
def pushLevelScalar (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (h : ScalarSquares l E)
    {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (DZ : SpCoefficientTowersAbelian l E Z) (DY : SpCoefficientTowersAbelian l E Y)
    (vZ : Evaluation l E b Z DZ) (vY : Evaluation l E b Y DY) (n : ℕ) :
    (forgetting l E Z DZ ⋙ fixedPushOrd l E p) ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n) ≅
      (ordinaryTowerPush l E b o p ⋙ forgetting l E Y DY) ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n) :=
  Functor.isoWhiskerLeft (spCoefficientEvaluation l E Z DZ.equivalence n)
      (ordinaryPushScalar l E h p n) ≪≫
    Functor.isoWhiskerRight
      (ordinaryPushEvaluation l E b o p DZ DY vZ vY n).symm
      (spCompletedEllRestriction l E Y n)

/-- Horizontal naturality of a family of finite-level comparisons.
Source: functor-category naturality; blueprint paragraph (2), strict systems.
(blueprint: lem-sp-compactification-ordinary-scalar-assembly). -/
def ScalarLevelCoherent {A C : Type*} [Category A] [Category C]
    (F G : A ⥤ (ℕᵒᵖ ⥤ C))
    (e : ∀ n : ℕ,
      F ⋙ (CategoryTheory.evaluation ℕᵒᵖ C).obj (op n) ≅
        G ⋙ (CategoryTheory.evaluation ℕᵒᵖ C).obj (op n)) : Prop :=
  ∀ (N : A) {m n : ℕᵒᵖ} (f : m ⟶ n),
    (F.obj N).map f ≫ (e n.unop).hom.app N =
      (e m.unop).hom.app N ≫ (G.obj N).map f

private def assembleLevelIso {A C : Type*} [Category A] [Category C]
    (F G : A ⥤ (ℕᵒᵖ ⥤ C))
    (e : ∀ n : ℕ,
      F ⋙ (CategoryTheory.evaluation ℕᵒᵖ C).obj (op n) ≅
        G ⋙ (CategoryTheory.evaluation ℕᵒᵖ C).obj (op n))
    (h : ScalarLevelCoherent F G e) : F ≅ G :=
  NatIso.ofComponents
    (fun N ↦ NatIso.ofComponents (fun n ↦ (e n.unop).app N) (fun f ↦ h N f))
    (by
      intro N M f
      ext n
      exact (e n.unop).hom.naturality f)

set_option maxHeartbeats 2000000 in
-- The nested evaluation isomorphisms require additional elaboration heartbeats.
/-- Horizontal coherence assembles the prescribed finite scalar comparisons into
ordinary isomorphisms of strict systems, with their finite normalizations.
Source: blueprint direct-image proof, paragraph (2), strict scalar comparison step.
(blueprint: lem-sp-compactification-ordinary-scalar-assembly).

Proof: for each input tower, apply NatIso.ofComponents to its finite components and
the given horizontal coherence. Naturality in the input follows from naturality of
each finite comparison. The open and push normalization equations cancel the finite
operation evaluation isomorphism and its inverse, inside restriction of scalars.
This argument retains every transition, including identities, before localization. -/
theorem compactificationOrdinaryScalarAssembly
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (h : ScalarSquares l E) {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (DX : SpCoefficientTowersAbelian l E X) (DZ : SpCoefficientTowersAbelian l E Z)
    (DY : SpCoefficientTowersAbelian l E Y)
    (vX : Evaluation l E b X DX) (vZ : Evaluation l E b Z DZ)
    (vY : Evaluation l E b Y DY)
    (hj : ScalarLevelCoherent (forgetting l E X DX ⋙ fixedOpenOrd l E j)
      (ordinaryTowerOpen l E b o j ⋙ forgetting l E Z DZ)
      (openLevelScalar l E b o h j DX DZ vX vZ))
    (hp : ScalarLevelCoherent (forgetting l E Z DZ ⋙ fixedPushOrd l E p)
      (ordinaryTowerPush l E b o p ⋙ forgetting l E Y DY)
      (pushLevelScalar l E b o h p DZ DY vZ vY)) :
    ∃ e : forgetting l E X DX ⋙ fixedOpenOrd l E j ≅
        ordinaryTowerOpen l E b o j ⋙ forgetting l E Z DZ,
    ∃ d : forgetting l E Z DZ ⋙ fixedPushOrd l E p ≅
        ordinaryTowerPush l E b o p ⋙ forgetting l E Y DY,
      (∀ (N : spCoefficientTowers l E X) (n : ℕ),
        (e.hom.app N).app (op n) ≫
            (spCompletedEllRestriction l E Z n).map
              ((ordinaryOpenEvaluation l E b o j DX DZ vX vZ n).hom.app N) =
          (ordinaryOpenScalar l E b h j n).hom.app
            ((spCoefficientEvaluation l E X DX.equivalence n).obj N)) ∧
      (∀ (N : spCoefficientTowers l E Z) (n : ℕ),
        (d.hom.app N).app (op n) ≫
            (spCompletedEllRestriction l E Y n).map
              ((ordinaryPushEvaluation l E b o p DZ DY vZ vY n).hom.app N) =
          (ordinaryPushScalar l E h p n).hom.app
            ((spCoefficientEvaluation l E Z DZ.equivalence n).obj N)) := by
  refine ⟨assembleLevelIso _ _ (openLevelScalar l E b o h j DX DZ vX vZ) hj,
    assembleLevelIso _ _ (pushLevelScalar l E b o h p DZ DY vZ vY) hp, ?_, ?_⟩
  · intro N n
    simp only [assembleLevelIso, NatIso.ofComponents_hom_app, openLevelScalar,
      Iso.app_hom, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Iso.symm_hom, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    rw [(spCompletedEllRestriction l E Z n).map_id]
    erw [Category.comp_id]
  · intro N n
    simp only [assembleLevelIso, NatIso.ofComponents_hom_app, pushLevelScalar,
      Iso.app_hom, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Iso.symm_hom, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    rw [(spCompletedEllRestriction l E Y n).map_id]
    erw [Category.comp_id]

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
