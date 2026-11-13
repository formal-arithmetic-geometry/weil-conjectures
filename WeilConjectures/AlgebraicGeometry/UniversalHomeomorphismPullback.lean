/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Universal-homeomorphism pullback coherence

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
-/

set_option linter.style.haveILetI false
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Invert the vertical equivalences in a commuting square of inverse images. -/
private theorem mixedSquareIso
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {U : A ⥤ B} {R : B ⥤ A} {P : C ⥤ D} {Q : D ⥤ C}
    (a : U ⊣ R) (b : P ⊣ Q) [IsIso a.counit] [IsIso b.unit]
    (S : B ⥤ D) (G : A ⥤ C) (e : U ⋙ S ≅ G ⋙ P) :
    Nonempty (S ⋙ Q ≅ R ⋙ G) := by
  exact ⟨(S ⋙ Q).leftUnitor.symm ≪≫
    Functor.isoWhiskerRight (asIso a.counit).symm (S ⋙ Q) ≪≫
    Functor.associator R U (S ⋙ Q) ≪≫
    Functor.isoWhiskerLeft R ((Functor.associator U S Q).symm ≪≫
      Functor.isoWhiskerRight e Q ≪≫ Functor.associator G P Q ≪≫
      Functor.isoWhiskerLeft G (asIso b.unit).symm ≪≫ G.rightUnitor)⟩

/-- Cancelling the compositor computes successive pullback along the named composite. -/
private theorem cohomologyMap_comp_cancel {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hh : h = f ≫ g)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (x : Sheaf.H F q) :
    Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} f g h hh).inv.app F) q
      (cohomologyMap f ((upperStar AddCommGrpCat.{u + 1} g).obj F) q
        (cohomologyMap g F q x)) = cohomologyMap h F q x := by
  subst h
  rw [(cohomologyPullbackFunctorial f g F q).2.1 x, ← Sheaf.H.map_comp_apply]
  simp only [Iso.hom_inv_id_app, Sheaf.H.map_id_apply]

/-- The base change of a universal homeomorphism `u` along any `g` is a universal homeomorphism
whose étale pullback adjunction has invertible unit and counit and which induces bijections on
étale cohomology. The inverse images and direct images along the pullback square commute up to
isomorphism, and the two cohomology pullbacks along the square agree. -/
theorem universalHomeomorphism_pullback {X X' : Scheme.{u}} (u : X' ⟶ X)
    [IsUniversalHomeomorphism u] :
    ∀ (Y : Scheme.{u}) (g : Y ⟶ X),
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
            (cohomologyMap g F q x)) := by
  intro Y g
  have : (upperStar AddCommGrpCat.{u + 1} (pullback.fst g u)).IsEquivalence :=
    isEquivalence_upperStar _ _
  have : (upperStar AddCommGrpCat.{u + 1} u).IsEquivalence :=
    isEquivalence_upperStar _ _
  have : (lowerStar (Type (u + 1)) u).IsEquivalence := isEquivalence_lowerStar _ _
  have : (lowerStar (Type (u + 1)) (pullback.fst g u)).IsEquivalence :=
    isEquivalence_lowerStar _ _
  let au := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    u.Etale (Type (u + 1)) X.smallEtaleTopology X'.smallEtaleTopology
  let ag := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    g.Etale (Type (u + 1)) X.smallEtaleTopology Y.smallEtaleTopology
  let ap := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (pullback.fst g u).Etale (Type (u + 1)) Y.smallEtaleTopology
      (pullback g u).smallEtaleTopology
  let as := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (pullback.snd g u).Etale (Type (u + 1)) X'.smallEtaleTopology
      (pullback g u).smallEtaleTopology
  let adjt := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (pullback.fst g u ≫ g).Etale (Type (u + 1)) X.smallEtaleTopology
      (pullback g u).smallEtaleTopology
  let es : Scheme.etaleSetPullback u ⋙ Scheme.etaleSetPullback (pullback.snd g u) ≅
      Scheme.etaleSetPullback g ⋙ Scheme.etaleSetPullback (pullback.fst g u) :=
    Adjunction.leftAdjointCompIso au as adjt
      (lowerStarComp (Type (u + 1)) (pullback.snd g u) u (pullback.fst g u ≫ g)
        (pullback.condition (f := g) (g := u))) ≪≫
    (Adjunction.leftAdjointCompIso ag ap adjt
      (lowerStarComp (Type (u + 1)) (pullback.fst g u) g)).symm
  let ea : upperStar AddCommGrpCat.{u + 1} u ⋙
      upperStar AddCommGrpCat.{u + 1} (pullback.snd g u) ≅
      upperStar AddCommGrpCat.{u + 1} g ⋙
        upperStar AddCommGrpCat.{u + 1} (pullback.fst g u) :=
    (upperStarComp AddCommGrpCat.{u + 1} (pullback.snd g u) u
      (pullback.fst g u ≫ g) (pullback.condition (f := g) (g := u))).symm ≪≫
    upperStarComp AddCommGrpCat.{u + 1} (pullback.fst g u) g
  refine ⟨inferInstance, inferInstance, inferInstance,
    fun G q ↦ cohomologyMap_bijective _ G q, ⟨es⟩, ?_, ⟨ea⟩, ?_, ?_⟩
  · exact mixedSquareIso au ap _ _ es
  · exact mixedSquareIso (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u)
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (pullback.fst g u)) _ _ ea
  · intro F q x
    rw [cohomologyMap_comp_cancel, cohomologyMap_comp_cancel]
end AlgebraicGeometry.Etale
