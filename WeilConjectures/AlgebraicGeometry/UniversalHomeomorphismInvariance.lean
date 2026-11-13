/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.EtaleSetPullbackSheafEquivalence
import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismIdentity
import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismComposition
import WeilConjectures.AlgebraicGeometry.UniversalHomeomorphismPullback
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance

set_option linter.style.haveILetI false

/-!
# Universal-homeomorphism invariance, with functorial compatibility

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Universal-homeomorphism invariance of the small etale sites, topoi and cohomology,
including identity, composition and base-change compatibility. -/
theorem universalHomeomorphism_invariance {X X' : Scheme.{u}} (u : X' ⟶ X)
    [IsUniversalHomeomorphism u] :
    u.Etale.IsEquivalence ∧
    (∀ (I : Type w) (V : X.Etale) (Vᵢ : I → X.Etale) (a : ∀ i, Vᵢ i ⟶ V),
      Sieve.ofArrows Vᵢ a ∈ X.smallEtaleTopology V ↔
        Sieve.ofArrows (fun i => u.Etale.obj (Vᵢ i)) (fun i => u.Etale.map (a i)) ∈
          X'.smallEtaleTopology (u.Etale.obj V)) ∧
    (∃ E : Sheaf X.smallEtaleTopology (Type (u + 1)) ≌
        Sheaf X'.smallEtaleTopology (Type (u + 1)),
      E.functor = Scheme.etaleSetPullback u ∧ E.inverse = lowerStar (Type (u + 1)) u) ∧
    IsIso (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).unit ∧
    IsIso (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).counit ∧
    (∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ),
      Function.Bijective (cohomologyMap u F q)) ∧
    (Nonempty (Scheme.etaleSetPullback (𝟙 X) ≅ 𝟭 _) ∧
      Nonempty (lowerStar (Type (u + 1)) (𝟙 X) ≅ 𝟭 _) ∧
      Nonempty (upperStar AddCommGrpCat.{u + 1} (𝟙 X) ≅ 𝟭 _) ∧
      Nonempty (lowerStar AddCommGrpCat.{u + 1} (𝟙 X) ≅ 𝟭 _) ∧
      ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
        (x : Sheaf.H F q),
        Sheaf.H.map ((upperStarId AddCommGrpCat.{u + 1} X).hom.app F) q
          (cohomologyMap (𝟙 X) F q x) = x) ∧
    (∀ (X'' : Scheme.{u}) (v : X'' ⟶ X'), IsUniversalHomeomorphism v →
      Nonempty (Scheme.etaleSetPullback (v ≫ u) ≅
        Scheme.etaleSetPullback u ⋙ Scheme.etaleSetPullback v) ∧
      Nonempty (lowerStar (Type (u + 1)) (v ≫ u) ≅
        lowerStar (Type (u + 1)) v ⋙ lowerStar (Type (u + 1)) u) ∧
      Nonempty (upperStar AddCommGrpCat.{u + 1} (v ≫ u) ≅
        upperStar AddCommGrpCat.{u + 1} u ⋙ upperStar AddCommGrpCat.{u + 1} v) ∧
      Nonempty (lowerStar AddCommGrpCat.{u + 1} (v ≫ u) ≅
        lowerStar AddCommGrpCat.{u + 1} v ⋙ lowerStar AddCommGrpCat.{u + 1} u) ∧
      ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
        (x : Sheaf.H F q),
        Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} v u).inv.app F) q
          (cohomologyMap v ((upperStar AddCommGrpCat.{u + 1} u).obj F) q
            (cohomologyMap u F q x)) = cohomologyMap (v ≫ u) F q x) ∧
    (∀ (Y : Scheme.{u}) (g : Y ⟶ X),
      IsUniversalHomeomorphism (pullback.fst g u) ∧
      IsIso (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (pullback.fst g u)).unit ∧
      IsIso (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (pullback.fst g u)).counit ∧
      (∀ (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ),
        Function.Bijective (cohomologyMap (pullback.fst g u) G q)) ∧
      Nonempty (Scheme.etaleSetPullback u ⋙ Scheme.etaleSetPullback (pullback.snd g u) ≅
        Scheme.etaleSetPullback g ⋙ Scheme.etaleSetPullback (pullback.fst g u)) ∧
      Nonempty (Scheme.etaleSetPullback (pullback.snd g u) ⋙
        lowerStar (Type (u + 1)) (pullback.fst g u) ≅
          lowerStar (Type (u + 1)) u ⋙ Scheme.etaleSetPullback g) ∧
      Nonempty (upperStar AddCommGrpCat.{u + 1} u ⋙
        upperStar AddCommGrpCat.{u + 1} (pullback.snd g u) ≅
          upperStar AddCommGrpCat.{u + 1} g ⋙
            upperStar AddCommGrpCat.{u + 1} (pullback.fst g u)) ∧
      Nonempty (upperStar AddCommGrpCat.{u + 1} (pullback.snd g u) ⋙
        lowerStar AddCommGrpCat.{u + 1} (pullback.fst g u) ≅
          lowerStar AddCommGrpCat.{u + 1} u ⋙ upperStar AddCommGrpCat.{u + 1} g) ∧
      ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
        (x : Sheaf.H F q),
        Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (pullback.snd g u) u
            (pullback.fst g u ≫ g) (pullback.condition (f := g) (g := u))).inv.app F) q
          (cohomologyMap (pullback.snd g u) ((upperStar AddCommGrpCat.{u + 1} u).obj F) q
            (cohomologyMap u F q x)) =
        Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (pullback.fst g u) g).inv.app F) q
          (cohomologyMap (pullback.fst g u) ((upperStar AddCommGrpCat.{u + 1} g).obj F) q
            (cohomologyMap g F q x))) := by
  letI : (u.Etale).IsEquivalence := Scheme.Hom.isEquivalence_etale u
  letI : (upperStar AddCommGrpCat.{u + 1} u).IsEquivalence :=
    isEquivalence_upperStar _ u
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro I V Vᵢ a
    simpa only [Sieve.functorPushforward_ofArrows] using
      (Scheme.Hom.functorPushforward_mem_smallEtaleTopology_iff u
        (Sieve.ofArrows Vᵢ a)).symm
  · refine ⟨(sheafEquivalence (Type (u + 1)) u).symm.changeFunctor
        (Classical.choice (etaleSetPullback_eq_sheafEquivalence u)), rfl, ?_⟩
    exact (lowerStar_eq_sheafEquivalence_functor (Type (u + 1)) u).symm
  · infer_instance
  · infer_instance
  · intro F q
    exact cohomologyMap_bijective u F q
  · exact ⟨universalHomeomorphism_identity u, universalHomeomorphism_composition u,
      universalHomeomorphism_pullback u⟩

end AlgebraicGeometry.Etale
