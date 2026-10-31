/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictCompactificationComparisonData

/-! # Bounded-below evaluation comparison for strict compactification data -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Evaluation of strict coefficient levels preserves the bounded-below
right-derived comparison, with the normalized push evaluation map.
Source: blueprint operations proof (2).
(blueprint: lem-sp-strict-plus-evaluation-realization).

Proof: conjugate the ordinary push evaluation square by the canonical
comparisons between unbounded and bounded-below right-derived functors.
The inclusion of bounded-below derived categories is fully faithful, so lift
the resulting equality through it. Expand the associators and use naturality
of the comparison isomorphisms; inverse cancellation leaves exactly the
normalized equation in `StrictPlusEvaluation`. This uses no faithfulness or
K-injectivity preservation assertion for evaluation itself. -/
theorem strictPlusEvaluationRealization (b : Base l E) (o : Operations l E b)
    [∀ T : Scheme.{u}, EnoughInjectives (S l E T)]
    [∀ (T : Scheme.{u}) (n : ℕ),
      EnoughInjectives (proEtaleRingModules T (proEtaleConstantRing T (R l E n)))] :
    StrictPlusEvaluation l E b o := by
  let comparison := fun {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) ↦
    Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (o.geometry f).push.rightDerivedFunctorPlus
          (ev l E Y n).mapDerivedCategoryPlusCompatibility ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (o.geometry f).push.rightDerivedFunctorPlusCompatibility (Ev l E Y n) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft DerivedCategory.Plus.ι ((o.geometry f).pushEvaluation n) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (ev l E X n).mapDerivedCategoryPlusCompatibility.symm
          (proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctor ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (ev l E X n).mapDerivedCategoryPlus
          (proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctorPlusCompatibility.symm ≪≫
        (Functor.associator _ _ _).symm)
  refine ⟨@comparison, ?_⟩
  intro X Y f n K
  dsimp only [comparison, Functor.fullyFaithfulCancelRight_hom_app]
  rw [CategoryTheory.Functor.map_preimage]
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rfl

end AlgebraicGeometry.ProEtale.SpTowerShriek
