/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate
import WeilConjectures.AlgebraicGeometry.RectangleQCohComparisonLifts
import WeilConjectures.AlgebraicGeometry.RectangleQCohOrdinaryCompatibility

/-! # Ordinary pasting comparisons for the iterated pullback

## References

* [Stacks Project, Tag 0ATR](https://stacks.math.columbia.edu/tag/0ATR)
* [Stacks Project, Tag 0ATM](https://stacks.math.columbia.edu/tag/0ATM)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry

-- The fixed signature names hL and hs, although the conclusion does not depend on their proofs.
/-- Direct-image and base comparisons compatible with a fixed canonical upper comparison. -/
theorem rectangle_ordinary_geometric_direct
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (g : S ⟶ Y) (h : T ⟶ S)
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f (h ≫ g)) (h ≫ g)
        (pullback.fst f (h ≫ g)) pullback.condition E.obj))
    (hβS : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition E.obj))
    (hβI : ∀ E : schemeDerivedQCohCategory (pullback f g),
      IsIso (schemeDerivedBaseChangeMap (pullback.snd f g) (pullback.snd (pullback.snd f g) h) h
        (pullback.fst (pullback.snd f g) h) pullback.condition E.obj))
    (k : pullback (pullback.snd f g) h ⟶ pullback f (h ≫ g))
    (hk₁ : k ≫ pullback.fst f (h ≫ g) =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g)
    (hk₂ : k ≫ pullback.snd f (h ≫ g) = pullback.snd (pullback.snd f g) h) :
    let U := qcPullback (pullback.fst f (h ≫ g))
    let L := qcPullback k
    let V := qcPullback (pullback.fst f g) ⋙
      qcPullback (pullback.fst (pullback.snd f g) h)
    let P := @qcDirectImage _ _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))) _ _
      (pullback.snd f (h ≫ g))
    let Q := @qcDirectImage _ _ _ _
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)) _ _
      (pullback.snd (pullback.snd f g) h)
    let B := qcPullback (h ≫ g)
    let H := qcPullback g ⋙ qcPullback h
    let α := qcInverseBaseChange f (h ≫ g) hβ
    let δ := qcInverseBaseChange f g hβS ≫ₕ
      @qcInverseBaseChange _ (pullback f g) S T _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _ h hβI
    ∀ (s : U ⋙ L ≅ V) (_ : L.IsEquivalence) (_ : ∀ E : schemeDerivedQCohCategory X,
      (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map (s.hom.app E) =
        (let comp := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition)))
         (comp k (pullback.fst f (h ≫ g))).hom.app E.obj ≫
           eqToHom (congrArg (fun v ↦ (derivedPullback v).obj E.obj) hk₁) ≫
           (comp (pullback.fst (pullback.snd f g) h)
             (pullback.fst f g)).inv.app E.obj)),
    ∃ (p : L ⋙ Q ≅ P) (b : B ≅ H),
      (∀ E : schemeDerivedQCohCategory X,
        Q.map (s.hom.app E) ≫ δ.app E =
          p.hom.app (U.obj E) ≫ α.app E ≫ b.hom.app ((qcDirectImage f).obj E)) := by
  classical
  intro U L V P Q B H α δ s hL hs
  obtain ⟨p, b, hp, hb⟩ := rectangle_qcoh_comparison_lifts f g h k hk₁ hk₂
  refine ⟨p, b, ?_⟩
  intro E
  let β := qcBaseChange f (h ≫ g)
  let βS := qcBaseChange f g
  let βI := @qcBaseChange _ (pullback f g) S T _
    (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
    (pullback.snd f g) _ _ h
  let γ := (qcPullback h).map (βS.app E) ≫ βI.app ((qcPullback (pullback.fst f g)).obj E)
  have hOrd : β.app E ≫ p.inv.app (U.obj E) ≫ Q.map (s.hom.app E) =
      b.hom.app ((qcDirectImage f).obj E) ≫ γ :=
    rectangle_qcoh_ordinary_compatibility f g h k hk₁ hk₂ s hL hs p b hp hb E
  have iβ : IsIso β := by
    have : ∀ E, IsIso (β.app E) := fun E ↦
      @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
        (schemeDerivedQCohProperty T).fullyFaithfulι _ _ (β.app E) (hβ E)
    exact NatIso.isIso_of_isIso_app β
  have iβS : IsIso βS := by
    have : ∀ E, IsIso (βS.app E) := fun E ↦
      @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
        (schemeDerivedQCohProperty S).fullyFaithfulι _ _ (βS.app E) (hβS E)
    exact NatIso.isIso_of_isIso_app βS
  have iβI : IsIso βI := by
    have : ∀ E, IsIso (βI.app E) := fun E ↦
      @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
        (schemeDerivedQCohProperty T).fullyFaithfulι _ _ (βI.app E) (hβI E)
    exact NatIso.isIso_of_isIso_app βI
  have : IsIso γ := by dsimp only [γ]; infer_instance
  have hα : α.app E = inv (β.app E) := by
    change (inv β).app E = _
    exact NatIso.isIso_inv_app β E
  have hδ : δ.app E = inv γ := by
    simp only [δ, TwoSquare.hComp_app, qcInverseBaseChange, NatIso.isIso_inv_app,
      γ, βI, βS, IsIso.inv_comp, Functor.map_inv]
  rw [hα, hδ]
  apply (cancel_mono γ).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hOrd]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_app]
  exact (Category.id_comp (Q.map (s.hom.app E))).symm


end AlgebraicGeometry
