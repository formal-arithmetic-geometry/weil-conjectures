/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleComplexClassDescent
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawAffineComplexPresentation

/-! # Raw affine cohomology classes descend to a stage

## References

* Stacks Project, Tags 09Z1 and 0EZM.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Every raw restricted-cohomology class over an affine etale object is a
pullback of a raw class at one stage. This assertion concerns derived Hom only;
no higher-direct-image sheaf or choice of sheafification comparison occurs
(Stacks, Tags 09Z1 and 0EZM). -/
theorem exists_higherDirectImage_raw_affine_class_rep {S : Scheme.{v}}
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
    ∀ (U : S.Etale) [IsAffine U.left]
      (z : (abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H)).obj (op U)),
      ∃ (i : I)
        (t : (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op U)),
        abelianHigherDirectImageRawPullback (c.π.app (op i)).left
          (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p (F i)
          (colimit H) ((eH i).inv ≫ colimit.ι H i) U t = z := by
  classical
  intro U _ z
  obtain ⟨D', c', hc', compact, quasiSeparated, affine, F', φ', hid, hcomp, a,
      hbelow, G, eG, hG, P, hP, K, eK, hK, L, hL, B, eB, hB, stageIso, limitIso,
      compatibility⟩ := exists_raw_affine_complex_presentation
    D c hc F φ hφid hφcomp H eH hH p U
  have : ∀ i, CompactSpace (D'.obj i) := compact
  have : ∀ i, QuasiSeparatedSpace (D'.obj i) := quasiSeparated
  have : ∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D'.map f) := affine
  obtain ⟨i, y, hy⟩ := exists_etale_complex_class_rep
    D' c' hc' F' φ' hid hcomp a hbelow
    G eG hG (p : ℤ) P hP K eK hK L hL B eB hB (limitIso.hom z)
  let t := (stageIso (op i)).inv y
  refine ⟨i.unop, t, ?_⟩
  have ht : (stageIso (op i)).hom t = y := by
    exact ConcreteCategory.congr_hom (stageIso (op i)).inv_hom_id y
  have hz := compatibility (op i) t
  rw [ht] at hz
  have he : limitIso.hom
      (abelianHigherDirectImageRawPullback (c.π.app (op i.unop)).left
        (D.obj (op i.unop)).hom c.pt.hom (Over.w (c.π.app (op i.unop))) p
        (F i.unop) (colimit H)
        ((eH i.unop).inv ≫ colimit.ι H i.unop) U t) = limitIso.hom z :=
    hz.symm.trans hy
  exact (ConcreteCategory.bijective_of_isIso limitIso.hom).1 he

end AlgebraicGeometry.Etale
