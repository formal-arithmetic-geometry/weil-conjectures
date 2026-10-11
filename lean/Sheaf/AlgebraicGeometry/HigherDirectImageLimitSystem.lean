/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageMap
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Higher direct images and inverse limits of schemes

Source: Stacks Project, Lemma 59.51.7, Tag 09Z1
(blueprint: sbc-lem-higher-direct-image-limit).
-/

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- For a directed inverse system of schemes over `S` with affine transitions and qcqs
structure maps, and any compatible system of abelian etale sheaves, the canonical map
from the colimit of their degree-`p` higher direct images to the higher direct image
of their colimit on the limit scheme is an isomorphism.
`H` records the pulled-back sheaf diagram via `eH` and `hH`; `K` records the higher
image diagram via `eK` and `hK`; `η` records the canonical comparison cocone via `hη`.
These are presentations of the diagrams and comparison map, not restrictions on the sheaves.
Source: Stacks, Tag 09Z1 (blueprint: sbc-lem-higher-direct-image-limit).

Proof:
1. By sbc-lem-higher-direct-image-presheaf (Tag 03Q8), higher direct images are
   sheafifications of `U ↦ H^p(U ×_S X_i, F_i)` and `U ↦ H^p(U ×_S X, F)`.
2. Cover each etale object by affine etale objects `V`. Base change to `V` gives
   qcqs schemes with affine transitions and limit `V ×_S X`. Apply
   lem-weil-pbc-etale-cohomology-limit-complex-systems (Tag 09YQ) to the sheaves
   as complexes concentrated in degree zero to identify the colimit cohomology.
3. These canonical identifications commute with restriction. Sheafification commutes
   with colimits, and the affine-basis identifications therefore identify the two
   sheafifications and prove that the canonical comparison is an isomorphism. -/
theorem isIso_higherDirectImage_limit_system {S : Scheme.{v}}
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
        ((eH i).inv ≫ colimit.ι H i)) :
    IsIso (colimit.desc K (Cocone.mk _ η)) :=
  sorry

end AlgebraicGeometry.Etale
