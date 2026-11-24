/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Adjunctions

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawAffineClassRep

/-! # Affine representatives of raw limit cohomology classes

## References

* Stacks Project, Tag 09Z1.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- On an affine etale object, a raw limit cohomology class is represented at a stage
(Stacks, Tags 09Z1 and 03Q8). -/
theorem exists_higherDirectImage_limit_affine_class_rep {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
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
    let T := (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
      (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))
    let P := (uliftYoneda.{v + 1} ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1} ⋙
      upperStar AddCommGrpCat.{v + 1} c.pt.hom ⋙
      DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj
          (((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H))⟦(p : ℤ)⟧)
    ∃ (e : (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj P ≅ T),
      ∀ (U : S.Etale) [IsAffine U.left] (z : P.obj (op U)),
        ∃ (i : I)
          (y : ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
            (R+(((D.obj (op i)).hom)_*[AddCommGrpCat.{v + 1}]).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj (F i)))).obj.obj (op U)),
          (abelianHigherDirectImageMap (c.π.app (op i)).left
            (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p (F i)
            (colimit H) ((eH i).inv ≫ colimit.ι H i)).hom.app (op U) y =
              ((toSheafify S.smallEtaleTopology P ≫ e.hom.hom).app (op U) z) := by
  obtain ⟨e, he⟩ := exists_abelianHigherDirectImage_natural_comparison S p
  refine ⟨e c.pt.hom (colimit H), ?_⟩
  intro U _ z
  obtain ⟨i, t, ht⟩ := exists_higherDirectImage_raw_affine_class_rep
    D c hc F φ hφid hφcomp H eH hH p U z
  refine ⟨i, (toSheafify S.smallEtaleTopology
    (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)) ≫
      (e (D.obj (op i)).hom (F i)).hom.hom).app (op U) t, ?_⟩
  rw [he, ht]
  rfl

end AlgebraicGeometry.Etale
