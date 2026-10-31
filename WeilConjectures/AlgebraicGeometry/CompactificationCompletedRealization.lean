/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactificationCompletedRealizationData

import WeilConjectures.AlgebraicGeometry.CompactificationStrictRealization
import WeilConjectures.AlgebraicGeometry.CompactificationFiniteProjectionModels
import WeilConjectures.AlgebraicGeometry.ProjectionTensorCoefficientComparison
import WeilConjectures.AlgebraicGeometry.SfIntegralConstructibleTriangulated
import WeilConjectures.ZetaSeries

import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization

/-! # Reconstruction and projection for completed compactification realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactificationCompletedRealization
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

variable (k : Type u) [Field k] (hl : IsUnit (l : k))
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [f.IsOver (Spec (.of k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Completed proper/open realization, with its whole strict-diagram normalization
and the completed counit projection identity, without a Tor-amplitude hypothesis.
Source: blueprint sk-prop-sf-pf-reduction, paragraph 2 and final paragraph;
Stacks 0A07, 0941, 0943, 0B56, 099I, 07A6
(blueprint: lem-fix-compactification-completed-realization).

Proof: (1) The coefficient DVR is Noetherian with finite perfect standard quotients;
finite-type schemes over k are Noetherian. (2) Strict open reduction preserves the
uniform cohomological interval and completeness, giving constructibility of j!K.
(3) Ordinary proper image commutes with the total derived limit of its strict
reduction tower; its augmentation is proper image of the completion unit.
(4) Apply proper image to the strict open comparison. Its quotient transitions
are exactly compactSupportRestrictedTransition; this constructs beta before limit.
(5) Integral direct-image constructibility gives constructibility of the image.
(6) The reduction/limit adjunction identifies each projection with proper perfect
projection followed by the normalized open tensor comparison, in that order.
(7) Constant-to-completed coefficient equivalence and strict tensor/pullback
substitution identify the completed operations with their common quotient towers.
(8) Coefficient restriction preserves the ordinary counit. The reflector Hom
bijection identifies its unique extension across chi with the completed counit.
(9) Completed projection coherence gives the total-limit equality of the actual
finite counit maps, with quotient transitions; no faithfulness of evaluations is
used. (10) The strict open tensor normalization has identity open restriction;
full faithfulness of extension by zero identifies it with the open factor of the
completed projection. Compose the proper identity and this open identity, then
conjugate by the reconstructed canonical realization. -/
theorem completedRealization [QuasiCompact c.i] :
    ∃ (aX : OpenFactorCoherence.Tensor l E X)
      (aZ : OpenFactorCoherence.Tensor l E c.Z) (aY : OpenFactorCoherence.Tensor l E Y)
      (b : OpenFactorCoherence.Pull l E f) (S : CoefficientDerivedSystemCalculus l E Y)
      (d : ∀ n : ℕ, FiniteCoordinates l E c n),
    Nonempty (CoefficientDerivedSystemCoherence l E Y S) ∧
    (∀ K : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E c.Z
        ((openExtension (completed l E) c.i).mapDerivedCategory.obj K.obj) ∧
      sfIntegralConstructible l E Y ((image (completed l E) c).obj K.obj)) ∧
    ∃ (β : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⋙
          strictReduction l E Y S ≅
        (sfIntegralConstructible l E X).ι ⋙ supportTower l E c k hl)
      (γ : sfCompactSupportFiniteIntegralFunctor l k hl c E ⋙
          (sfIntegralConstructible l E Y).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ supportTower l E c k hl ⋙
          coefficientConstantTowerLimit l E Y),
    (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      γ.hom.app K ≫ (coefficientConstantTowerProjection l E Y n).app
          ((supportTower l E c k hl).obj K.obj) ≫
          (supportEvaluation l E c k hl n).hom.app K.obj =
        (coefficientFiniteAdjunction l E Y n).unit.app
            ((sfCompactSupportFiniteIntegralFunctor l k hl c E).obj K).obj ≫
          (scalarReductionDerivedRestriction l E Y n).map
            (sfCompactSupportFiniteReductionIso l k hl c E K n).hom) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X) (m n : ℕ) (h : n ≤ m),
      (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
          m n h).app ((supportTower l E c k hl).obj K.obj) ≫
          (supportEvaluation l E c k hl n).hom.app K.obj =
        (supportEvaluation l E c k hl m).hom.app K.obj ≫
          compactSupportRestrictedTransition l E c m n h K.obj) ∧
    SfQcqsCompactSupportRealizationSpec l E k hl c
      (sfQcqsCompactSupportRealization l E k hl c) ∧
    (∀ K : sfIntegralConstructibleCategory l E X,
      (sfQcqsCompactSupportRealization l E k hl c).hom.app K =
        S.adjunction.unit.app ((image (completed l E) c).obj K.obj) ≫
          (coefficientConstantTowerLimit l E Y).map (β.hom.app K) ≫ γ.inv.app K) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      (coefficientConstantTowerEvaluation l E Y n).map (β.hom.app K) ≫
          (supportEvaluation l E c k hl n).hom.app K.obj =
        (strictEvaluation l E S n).hom.app ((image (completed l E) c).obj K.obj) ≫
          (scalarReductionDerivedRestriction l E Y n).map
            ((scalarReductionDerivedExtension l E Y n).map
                ((sfQcqsCompactSupportRealization l E k hl c).hom.app K) ≫
              (sfCompactSupportFiniteReductionIso l k hl c E K n).hom)) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      (scalarReductionDerivedExtension l E Y n).map
          ((sfQcqsCompactSupportRealization l E k hl c).hom.app K) ≫
          (sfCompactSupportFiniteReductionIso l k hl c E K n).hom =
        (finiteReductionIso l E Y n).inv.app ((image (completed l E) c).obj K.obj) ≫
          orderedReduction l E c n K.obj ≫
          (finiteImageIso l E n c).hom.app
            ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj K.obj) ≫
          (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1))
            c).map ((finiteReductionIso l E X n).hom.app K.obj)) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X)
      (L : sfIntegralConstructibleCategory l E Y)
      (hQ : sfIntegralConstructible l E X (projectionArgument l E K.obj L.obj))
      (_hV : sfIntegralConstructible l E Y (projectionSource l E c K.obj L.obj)),
      let Q : sfIntegralConstructibleCategory l E X := ⟨_, hQ⟩
      ∃ π : projectionSource l E c K.obj L.obj ⟶
          (image (completed l E) c).obj Q.obj,
        ((aY.chi l E).app ((image (completed l E) c).obj K.obj, L.obj) ≫ π =
          augmentedProjection l E c aX aZ aY b K.obj L.obj) ∧
        (∀ π' : projectionSource l E c K.obj L.obj ⟶ (image (completed l E) c).obj Q.obj,
          (aY.chi l E).app ((image (completed l E) c).obj K.obj, L.obj) ≫ π' =
            augmentedProjection l E c aX aZ aY b K.obj L.obj → π' = π) ∧
        (∀ n : ℕ, FiniteProjectionEquation l E c n (d n) aX aZ aY b K.obj L.obj) ∧
        (IsIso (strictSourceUnit l E c S aY K.obj L.obj)) ∧
        (∀ (h : IsIso (strictSourceUnit l E c S aY K.obj L.obj)),
          letI := h
          (strictReduction l E Y S).map π =
            inv (strictSourceUnit l E c S aY K.obj L.obj) ≫
              strictProjection l E c S aX aZ aY b K.obj L.obj) ∧
        (∀ (h : IsIso (strictSourceUnit l E c S aY K.obj L.obj)),
          letI := h
          let dc := sfQcqsCompactSupportRealization l E k hl c
          let ρ := (integralCompletedTensor.{u, u} l E Y).map
              (Prod.mkHom (dc.inv.app K) (𝟙 L.obj)) ≫
            S.adjunction.unit.app (projectionSource l E c K.obj L.obj) ≫
              (coefficientConstantTowerLimit l E Y).map
                (inv (strictSourceUnit l E c S aY K.obj L.obj) ≫
                  strictProjection l E c S aX aZ aY b K.obj L.obj ≫ β.hom.app Q) ≫
              γ.inv.app Q
          π ≫ dc.hom.app Q =
            (integralCompletedTensor.{u, u} l E Y).map
                (Prod.mkHom (dc.hom.app K) (𝟙 L.obj)) ≫ ρ)) := by
  classical
  obtain ⟨aX, aZ, aY, b, d, hd⟩ := finiteProjectionModels l E c
  obtain ⟨S, hS, hopen, β, γ, hγ, hdc, hβ⟩ := strictRealization l E c k hl
  have hspec : SfQcqsCompactSupportRealizationSpec l E k hl c
      (sfQcqsCompactSupportRealization l E k hl c) :=
    (sfQcqsCompactSupportRealization_spec l E k hl c)
  have hconstructible (K : sfIntegralConstructibleCategory l E X) :
      sfIntegralConstructible l E Y ((image (completed l E) c).obj K.obj) :=
    (sfIntegralConstructible l E Y).prop_of_iso
      ((sfQcqsCompactSupportRealization l E k hl c).app K).symm
      ((sfCompactSupportFiniteIntegralFunctor l k hl c E).obj K).property
  refine ⟨aX, aZ, aY, b, S, d, hS, fun K ↦ ⟨hopen K, hconstructible K⟩,
    β, γ, hγ, ?_, hspec,
    hdc, hβ, ?_, ?_⟩
  · intro K m n h
    exact (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (exists_compactSupportReductionTower l E k X Y f hl c))).2.2).2).2).1
          m n h K.obj
  · intro K n
    simpa only [comparison_factorization, orderedReduction, push, Category.assoc] using hspec K n
  · intro K L hQ _hV
    let Q : sfIntegralConstructibleCategory l E X := ⟨_, hQ⟩
    let PK : sfIntegralConstructibleCategory l E Y := ⟨_, hconstructible K⟩
    let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
    let : ∀ y : Y, Invertible (l : Y.residueField y) := fun y ↦
      (by simpa only [map_natCast] using
        hl.map ((Y ↘ Spec (.of k)).residueFieldAlgebraMap y) :
          IsUnit (l : Y.residueField y)).invertible
    let : IsIso ((aY.chi l E).app (PK.obj, L.obj)) :=
      ProjectionTensorCoefficient.completion_isIso l E Y aY PK L
    let χ := (aY.chi l E).app (PK.obj, L.obj)
    let π : projectionSource l E c K.obj L.obj ⟶
        (image (completed l E) c).obj Q.obj :=
      inv χ ≫ augmentedProjection l E c aX aZ aY b K.obj L.obj
    have hπ : χ ≫ π = augmentedProjection l E c aX aZ aY b K.obj L.obj := by
      simp [π]
    let : IsIso (strictSourceUnit l E c S aY K.obj L.obj) := by
      change IsIso ((strictReduction l E Y S).map χ)
      infer_instance
    have hm : (strictReduction l E Y S).map π =
        inv (strictSourceUnit l E c S aY K.obj L.obj) ≫
          strictProjection l E c S aX aZ aY b K.obj L.obj := by
      have he : strictSourceUnit l E c S aY K.obj L.obj ≫
          (strictReduction l E Y S).map π =
            strictProjection l E c S aX aZ aY b K.obj L.obj := by
        change (strictReduction l E Y S).map χ ≫ _ = _
        rw [← Functor.map_comp, hπ]
        rfl
      rw [← he]
      simp
    refine ⟨π, hπ, ?_, hd K L, ?_, fun _ ↦ hm, ?_⟩
    · intro π' hπ'
      apply (cancel_epi χ).mp
      exact hπ'.trans hπ.symm
    · change IsIso ((strictReduction l E Y S).map χ)
      infer_instance
    · intro h
      let := h
      dsimp only
      have hmβ := congrArg (fun z ↦ z ≫ β.hom.app Q) hm
      rw [show inv (strictSourceUnit l E c S aY K.obj L.obj) ≫
          strictProjection l E c S aX aZ aY b K.obj L.obj ≫ β.hom.app Q =
            (strictReduction l E Y S).map π ≫ β.hom.app Q from
          by simpa only [Category.assoc] using hmβ.symm, hdc Q]
      have ht : (integralCompletedTensor.{u, u} l E Y).map
          (Prod.mkHom ((sfQcqsCompactSupportRealization l E k hl c).hom.app K)
            (𝟙 L.obj)) ≫
          (integralCompletedTensor.{u, u} l E Y).map
          (Prod.mkHom ((sfQcqsCompactSupportRealization l E k hl c).inv.app K)
            (𝟙 L.obj)) = 𝟙 _ := by
        rw [← Functor.map_comp]
        simp only [prod_comp, Iso.hom_inv_id_app, Category.id_comp, ← prod_id]
        exact (integralCompletedTensor.{u, u} l E Y).map_id _
      simp only [← Category.assoc, ht, Category.id_comp]
      rw [Functor.map_comp]
      have hn := S.adjunction.unit.naturality π
      dsimp only [Functor.id_map, Functor.comp_map] at hn
      simpa only [Category.assoc, Q, strictReduction, coefficientSequenceLimit,
        Functor.comp_map] using congrArg
        (fun z ↦ z ≫ (coefficientConstantTowerLimit l E Y).map (β.hom.app Q) ≫
          γ.inv.app Q) hn

end WeilConjectures.CompactificationCompletedRealization
