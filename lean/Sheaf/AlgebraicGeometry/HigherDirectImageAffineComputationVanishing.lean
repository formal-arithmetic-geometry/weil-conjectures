/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit

/-! # Affine computation for eventual vanishing of higher direct images

Source: Stacks Project, Tags 09Z1, 03Q8 and 0EZM.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- On an affine etale object, a section killed at the limit dies at a later stage.
Source: Stacks Project, Tag 09Z1, proof of lemma-relative-colimit; Tag 03Q8;
Tag 0EZM (blueprint: lem-sbc-higher-direct-image-affine-computation-vanishing).

Proof: Use the natural cohomology-presheaf comparison of Tag 03Q8 at each stage
and at the limit. Locally lift the section to cohomology representatives. Naturality
for the derived adjunction unit and coefficient maps identifies the canonical maps
with the displayed maps. Local injectivity of sheafification refines the cover so that the
limit representatives are zero. Refine by affine etale objects. For each member W,
base change the scheme cone along W -> S: its stages are qcqs since their structure
morphisms to affine W are qcqs, its transitions remain affine, and its cone remains
limiting. Exact inverse image preserves the coefficient colimit and degree-zero
complexes. Apply complex cohomology continuity with lower bound zero. Injectivity
of the colimit comparison and the filtered group colimit equality criterion kill
each representative at a later stage, hence also its sheafification image.
Quasi-compactness of the original affine object gives a finite subcover; directedness
moves all these witnesses to one stage. Naturality restricts its image to zero on
every member, and sheaf separatedness makes the section zero. For p = 0 use ordinary
sections; on the empty affine object separatedness gives zero immediately.
Only the cohomology-group colimit comparison on W is used; no colimit of higher images
is needed.
-/
theorem exists_higherDirectImage_affine_computation_eq_zero {S : Scheme.{v}}
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
    [HasColimit H] (p : ℕ)
    (V : S.Etale) [IsAffine V.left] (i : I)
    (y : ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
      (R+(((D.obj (op i)).hom)_*[AddCommGrpCat.{v + 1}]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (F i)))).obj.obj (op V))
    (hy : (abelianHigherDirectImageMap (c.π.app (op i)).left
      (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p
      (F i) (colimit H) ((eH i).inv ≫ colimit.ι H i)).hom.app (op V) y = 0) :
    ∃ (j : I) (f : i ⟶ j),
      (abelianHigherDirectImageMap (D.map f.op).left (D.obj (op i)).hom
        (D.obj (op j)).hom (Over.w (D.map f.op)) p (F i) (F j) (φ f)).hom.app
          (op V) y = 0 := by sorry

end AlgebraicGeometry.Etale
