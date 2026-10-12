/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf

/-! # Affine restrictions of raw classes eventually vanish

Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-higher-direct-image-raw-affine-restriction-vanishing).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- On an affine etale test object a zero raw limit class dies at a later stage.
Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-higher-direct-image-raw-affine-restriction-vanishing).

Proof: Commute raw pullback with restriction to W by the naturality of inverse-image
composition and the comparison with the single functor. Base change the cone to W.
Since W is affine, its base changes with the qcqs stage schemes are qcqs; affine
transition maps and the limit property are preserved by base change. Restrict the
coefficient system; inverse image preserves its colimit and its coherence maps.
Place every coefficient sheaf in degree zero. Derived adjunction for etale
restriction identifies the raw Hom groups with cohomology on these base changes:
the free abelian sheaf on W represents sections, and the exact left adjoint of
restriction makes this identification compatible with pullback and coefficients.
Apply complex cohomology continuity (Tag 0EZM) with lower bound zero. Its canonical
colimit comparison is injective. The filtered abelian-group colimit equality
criterion therefore gives j and i → j with zero image of the restricted class.
The single and shift comparisons identify that image with the stated raw map.
Naturality of raw pullback with restriction then preserves this same zero class
on every V → W: the restrictions are precomposition, and the inverse-image
composition and single-functor comparisons are natural transformations. Their
naturality squares, mapped into the derived category, commute with this
precomposition. Thus the stage j and arrow obtained above work on all further
restrictions. Degree zero is section continuity; the empty affine object has zero group. -/
theorem exists_higherDirectImage_raw_affine_restriction_eq_zero {S : Scheme.{v}}
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
    [HasColimit H] (p : ℕ) (U : S.Etale) (i : I)
    (z : (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op U))
    (W : S.Etale) (q : W ⟶ U) [IsAffine W.left]
    (hz : (abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H)).map q.op
      (abelianHigherDirectImageRawPullback (c.π.app (op i)).left
        (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p (F i)
        (colimit H) ((eH i).inv ≫ colimit.ι H i) U z) = 0) :
    ∃ (j : I) (f : i ⟶ j), ∀ (V : S.Etale) (a : V ⟶ W),
      abelianHigherDirectImageRawPullback (D.map f.op).left (D.obj (op i)).hom
        (D.obj (op j)).hom (Over.w (D.map f.op)) p (F i) (F j) (φ f) V
          ((abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).map
            (a ≫ q).op z) = 0 := by sorry

end AlgebraicGeometry.Etale
