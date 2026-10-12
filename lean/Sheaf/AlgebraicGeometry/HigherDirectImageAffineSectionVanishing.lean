/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit

/-! # Classes in fibers of higher direct images under scheme limits

Source: Stacks Project, Tag 09Z1, affine-local injectivity step.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- A section on an affine etale object killed by the limit comparison is killed at a stage.
Source: Stacks Project, Tag 09Z1, proof on qcqs etale objects; Tag 03Q8.
(blueprint: sbc-lem-higher-direct-image-affine-section-vanishing).

Proof:
1. Write each higher direct image as the sheafification of its restricted cohomology
   presheaf, using Tag 03Q8. The identifications are natural for the canonical maps
   defined by derived adjunction. Thus `hK` and `hη` identify the sheaf maps with
   the maps of those cohomology presheaves.
2. On a qcqs etale object U, base change of D and c gives qcqs schemes, affine
   transitions, and a limiting cone. Exact inverse image commutes with colimits,
   compositions, and degree-zero complexes. The pulled-back sheaves therefore
   satisfy the hypotheses of complex cohomology continuity, with lower bound zero.
   Its comparison is exactly the canonical comparison on restricted cohomology.
   In particular a cohomology class mapped to zero at the limit dies at a stage.
3. For the given section on the affine V, take an etale cover on which it lifts to
   the restricted cohomology presheaf. Since its limit image is the zero sheaf
   section, refine the cover so the limit cohomology representatives are zero.
   Refine again by affines. Quasi-compactness of V gives a finite subcover. Apply
   step 2 on each affine member; directedness gives a common later stage. The
   stage image of the original section restricts to zero on each member, so it is
   zero by the separatedness of a sheaf. This proves the assertion.

For p = 0 the same argument uses ordinary sections. For empty V its section group
is zero. No affine or qcqs assumption on S itself is used. -/
theorem exists_higherDirectImage_affine_section_eq_zero {S : Scheme.{v}}
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
    (K : I ⥤ Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eK : ∀ i : I, K.obj i ≅
      (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+(((D.obj (op i)).hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (F i))))
    (hK : ∀ {i j : I} (f : i ⟶ j), K.map f =
      (eK i).hom ≫ abelianHigherDirectImageMap (D.map f.op).left
        (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
        (F i) (F j) (φ f) ≫ (eK j).inv)
    [HasColimit K]
    (η : K ⟶ (Functor.const I).obj
      ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+((c.pt.hom)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (colimit H)))))
    (hη : ∀ i : I, η.app i = (eK i).hom ≫
      abelianHigherDirectImageMap (c.π.app (op i)).left (D.obj (op i)).hom c.pt.hom
        (Over.w (c.π.app (op i))) p (F i) (colimit H)
        ((eH i).inv ≫ colimit.ι H i)) (V : S.Etale)
    [IsAffine V.left] :
    ∀ (i : I) (z : (K.obj i).obj.obj (op V)),
      (η.app i).hom.app (op V) z = 0 →
      ∃ (j : I) (f : i ⟶ j), (K.map f).hom.app (op V) z = 0 := by
  sorry

end AlgebraicGeometry.Etale
