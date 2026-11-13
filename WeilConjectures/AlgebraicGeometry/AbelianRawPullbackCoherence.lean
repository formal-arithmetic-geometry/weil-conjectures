/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.AbelianRawPullbackCoherenceBase
import WeilConjectures.AlgebraicGeometry.AbelianRawPullbackCoherenceExtend

/-! # Coherence of varying-coefficient raw pullbacks

## References

* Stacks Project, Tags 03Q8 and 09Z1
-/

@[expose] public section


universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Raw pullback obeys coefficient identity, composition and cocone laws
(Stacks, Tags 09Z1 and 03CB). -/
theorem abelianRawPullback_coherent {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ) :
    ∃ (τ : ∀ {i j : I} (_f : i ⟶ j),
        abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i) ⟶
          abelianHigherDirectImageRawPresheaf (D.obj (op j)).hom p (F j))
      (β : ∀ i : I, abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i) ⟶
        abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H)),
      (∀ {i j : I} (f : i ⟶ j) (V : S.Etale) (t :
          (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op V)),
        (τ f).app (op V) t = abelianHigherDirectImageRawPullback (D.map f.op).left
          (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
          (F i) (F j) (φ f) V t) ∧
      (∀ (i : I) (V : S.Etale) (t :
          (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op V)),
        (β i).app (op V) t = abelianHigherDirectImageRawPullback (c.π.app (op i)).left
          (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p
          (F i) (colimit H) ((eH i).inv ≫ colimit.ι H i) V t) ∧
      (∀ i : I, τ (𝟙 i) = 𝟙 _) ∧
      (∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), τ (f ≫ g) = τ f ≫ τ g) ∧
      (∀ {i j : I} (f : i ⟶ j), τ f ≫ β j = β i) := by
  rcases abelianRawPullback_coherent_base D c F φ hφid hφcomp H eH hH p with
    ⟨τ, β, hτ, hβ, hid, hcomp⟩
  refine ⟨τ, β, hτ, hβ, hid, hcomp, ?_⟩
  exact abelianRawPullback_coherent_extend D c F φ hφid hφcomp H eH hH p
    τ β hτ hβ

end AlgebraicGeometry.Etale
