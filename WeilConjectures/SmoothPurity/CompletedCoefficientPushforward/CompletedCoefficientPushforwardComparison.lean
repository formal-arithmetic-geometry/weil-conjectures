/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardSites
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientStructureMap
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientDirectImageDiagrams
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedReductionAugmentationIso
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedDirectImagePreservesCompleteness

/-! # Completed-coefficient direct image and reconstruction

The canonical completed/constant and finite-coefficient direct-image comparisons, with
restriction coherence, strict derived diagrams and complete reconstruction.

## Implementation details

A strict diagram of complexes is realized as a complex of diagrams degreewise, with identity
maps as the strict realization isomorphism. The reduction augmentation is the unique chain map
into the inverse limit induced by the tensor units `x ↦ 1 ⊗ x`. Reconstruction of a complete
object combines this augmentation with the normalized derived-limit unit and
`limitComparison`.

## References

* Stacks Project, Tags 0D6E, 0A07 and 099N (1),(4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b av bv c cv z zv d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedCoefficientPushforward
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y : Scheme.{t}} (f : X ⟶ Y)

private instance towerLimitAdditive (W : Scheme.{t}) : (ordinaryTowerLimit l E W).Additive := by
  constructor
  intro X Y f g
  apply limit.hom_ext
  intro n
  simp only [ordinaryTowerLimit, lim_map, limMap_π, Preadditive.add_comp, NatTrans.app_add,
    Preadditive.comp_add]

private theorem strictComplexTower_exists
    {C : Type a} [Category.{av} C] [HasZeroMorphisms C]
    (T : ℕᵒᵖ ⥤ CochainComplex C ℤ) :
    ∃ P : CochainComplex (ℕᵒᵖ ⥤ C) ℤ, Nonempty (P.asFunctor ≅ T) := by
  let P : CochainComplex (ℕᵒᵖ ⥤ C) ℤ :=
    { X := fun i ↦ T ⋙ HomologicalComplex.eval C (.up ℤ) i
      d := fun i j ↦
        { app := fun n ↦ (T.obj n).d i j
          naturality := fun n m f ↦ (T.map f).comm i j }
      shape := fun i j h ↦ by
        ext n
        exact (T.obj n).shape i j h
      d_comp_d' := fun i j k _ _ ↦ by
        ext n
        exact (T.obj n).d_comp_d i j k }
  refine ⟨P, ⟨NatIso.ofComponents (fun n ↦ ?_) ?_⟩⟩
  · exact HomologicalComplex.Hom.isoOfComponents (fun i ↦ Iso.refl _) (by
      intro i j h
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl)
  · intro n m f
    ext i
    simp
    rfl

private theorem reductionAugmentation_existsUnique (W : Scheme.{t})
    (P : CochainComplex (Mod W (R l E W)) ℤ)
    (C : CochainComplex (ℕᵒᵖ ⥤ Mod W (R l E W)) ℤ)
    (e : C.asFunctor ≅ unrestrictedIntegralComplexTower l E W P) :
    ∃! a : P ⟶ ((ordinaryTowerLimit l E W).mapHomologicalComplex (.up ℤ)).obj C,
      IsReductionAugmentation l E W P C e a := by
  let γ (n : ℕ) : P ⟶ (unrestrictedIntegralComplexTower l E W P).obj (op n) :=
    unrestrictedTowerUnit l E W P n
  have hγ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ) (x : (P.X i).val.obj U) :
      ((γ n).f i).val.app U x = unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x :=
    unrestrictedTowerUnit_condition l E W P n i U x
  let b₀ : (Functor.const ℕᵒᵖ).obj P ⟶ unrestrictedIntegralComplexTower l E W P :=
    NatTrans.ofOpSequence γ (by
      intro n
      simp only [Functor.const_obj_map]
      symm
      simp only [unrestrictedIntegralComplexTower, Functor.ofOpSequence_map_homOfLE_succ]
      ext i U x
      change (((unrestrictedIntegralTransition l E W n).app P).f i).val.app U
          (((γ (n + 1)).f i).val.app U x) = ((γ n).f i).val.app U x
      rw [hγ, hγ]
      simpa [unrestrictedIntegralTransition] using
        (unrestrictedIntegralTransition_existsUnique l E W n).exists.choose_spec P i U 1 x)
  let b := b₀ ≫ e.inv
  let a : P ⟶ ((ordinaryTowerLimit l E W).mapHomologicalComplex (.up ℤ)).obj C :=
    { f := fun i ↦ limit.lift (C.X i)
        { pt := P.X i
          π :=
            { app := fun n ↦ (b.app n).f i
              naturality := fun n m f ↦ by
                have h := congrArg (fun k ↦ k.f i) (b.naturality f)
                simpa only [Functor.const_obj_map, HomologicalComplex.comp_f,
                  HomologicalComplex.id_f, HomologicalComplex.asFunctor,
                  Category.id_comp] using h } }
      comm' := fun i j _ ↦ by
        apply limit.hom_ext
        intro n
        simp only [Functor.mapHomologicalComplex_obj_d, ordinaryTowerLimit,
          Category.assoc, lim_map, limMap_π, limit.lift_π_assoc, limit.lift_π]
        exact (b.app n).comm i j }
  have ha (i : ℤ) (n : ℕᵒᵖ) : a.f i ≫ limit.π (C.X i) n = (b.app n).f i :=
    limit.lift_π _ _
  have haug : IsReductionAugmentation l E W P C e a := by
    intro n i U x
    rw [← Category.assoc, ha]
    change (((b.app (op n)).f i ≫ (e.hom.app (op n)).f i).val.app U) x = _
    have hb := congrArg (fun k ↦ (k.app (op n)).f i)
      (show b ≫ e.hom = b₀ by simp [b])
    rw [← HomologicalComplex.comp_f]
    change (((b ≫ e.hom).app (op n)).f i).val.app U x = _
    rw [hb]
    exact hγ n i U x
  refine ⟨a, haug, ?_⟩
  intro a' ha'
  apply HomologicalComplex.hom_ext
  intro i
  apply limit.hom_ext
  intro n
  apply (cancel_mono ((e.hom.app n).f i)).mp
  ext U x
  exact (ha' n.unop i U x).trans (haug n.unop i U x).symm

/-- The canonical completed/constant and finite-coefficient direct-image comparisons,
including restriction coherence, strict derived diagrams and complete reconstruction. -/
theorem comparison (p : ℕ) [Fact p.Prime] (_hlp : l ≠ p) :
    Nonempty (ComparisonData l E f) := by
  obtain ⟨source⟩ := siteData_exists l E X
  obtain ⟨target⟩ := siteData_exists l E Y
  obtain ⟨c, ⟨hc, hc0⟩, _⟩ := completedStructure_existsUnique (l := l) (E := E) (f := f)
  obtain ⟨D, _, _, _⟩ := directImageDiagrams_exists l E f source target c hc hc0
  refine ⟨{ toDiagramComparisonData := D
            preservesComplete := ?_
            strictReductionExists := ?_
            reductionAugmentation := ?_
            reconstruction := ?_ }⟩
  · intro K hK
    exact directImage_preservesComplete l E p _hlp f D.structureMap
      D.structureProjection D.completedImage K hK
  · intro P
    exact strictComplexTower_exists (unrestrictedIntegralComplexTower l E X P)
  · intro P C e
    exact reductionAugmentation_existsUnique l E X P C e
  · intro K P hP hflat r C e a ha hK
    have := reductionAugmentation_isIso l E p _hlp X D.source.toSiteLimitData
      K P hP hflat r C e a ha hK
    infer_instance

end WeilConjectures.CompletedCoefficientPushforward
