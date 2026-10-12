/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageMap
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf

/-! # Natural comparison for abelian higher direct images

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: lem-sbc-abelian-higher-direct-image-natural-comparison).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The derived-Hom presentation of restricted cohomology, for degree-zero coefficients.
This is the presheaf in Tag 03Q8, before sheafification. -/
noncomputable abbrev abelianHigherDirectImageRawPresheaf {S Y : Scheme.{v}}
    (h : Y ⟶ S) (p : ℕ) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :=
  (uliftYoneda.{v + 1} ⋙
    (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1} ⋙
    upperStar AddCommGrpCat.{v + 1} h ⋙
    DerivedCategory.Plus.singleFunctor _ 0).op ⋙
      preadditiveYoneda.obj (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧)

/-- Pull back a raw derived-Hom class and then apply the coefficient map.
All factors are actual functorial constructions: pullback composition, comparison
with the degree-zero single functor, pullback of the class, shift comparison, and
shifted coefficient map. Source: Stacks Project, Tag 09Z1, cohomology comparison. -/
noncomputable def abelianHigherDirectImageRawPullback {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F') (U : S.Etale)
    (z : (abelianHigherDirectImageRawPresheaf h p F).obj (op U)) :
    (abelianHigherDirectImageRawPresheaf h' p F').obj (op U) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{v + 1} a h h' w.symm).hom.app _) ≫
    (((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    D+((a)^*[AddCommGrpCat.{v + 1}]).map z ≫
    (D+((a)^*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (shiftFunctor _ (p : ℤ)).map
      ((((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map φ)

/-- The sheafification comparison can be chosen naturally for every structure map
and coefficient sheaf over a fixed base, and intertwines raw pullback with the
canonical higher-direct-image map.
Source: Stacks Project, Tag 03Q8 (natural presheaf comparison), and Tag 09Z1
(the comparison maps in the proof).
(blueprint: lem-sbc-abelian-higher-direct-image-natural-comparison).

Proof: For h : Y → S and F, use derived adjunction to send a raw class to a map
from the free abelian representable in D⁺(S). Take degree-zero homology after
shifting by p, use the shift comparison of Rh_*, and evaluate the resulting map
from the free sheaf at its identity generator. This is a natural morphism from
the raw presheaf to R^p h_*F. To see that its sheafification is an isomorphism,
represent the derived object by a bounded-below injective complex. Locally every
homology section lifts to a cycle, hence to a map from the free sheaf. If the
homology section of a class is zero, locally its cycle is a boundary and the
associated chain map is null-homotopic. Thus the morphism is locally bijective,
and the sheafification adjunction gives the isomorphism. This is the construction
used in nonempty_higherDirectImage_iso_sheafification_abelian_single, rather than
an arbitrary isomorphism obtained solely from its Nonempty conclusion.
For a : Y' → Y and a coefficient map, expand derived adjunction as its unit
followed by direct image of the class. Naturality of the unit moves the class
past pullback; the triangle identity cancels the counit. Pullback composition
and its single-functor comparison then give exactly the factors in
abelianHigherDirectImageMap. Shift compatibility moves the coefficient map
through the shifted class. Taking homology and evaluating the identity generator
proves the displayed equality. This argument is uniform in h, F and a, and
requires no affine, qcqs or inverse-limit hypothesis. -/
theorem exists_abelianHigherDirectImage_natural_comparison (S : Scheme.{v}) (p : ℕ) :
    ∃ e : ∀ {Y : Scheme.{v}} (h : Y ⟶ S)
      (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}),
      (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
          (abelianHigherDirectImageRawPresheaf h p F) ≅
        (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
          (R+((h)_*[AddCommGrpCat.{v + 1}]).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)),
      ∀ {Y Y' : Scheme.{v}} (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S)
        (w : a ≫ h = h')
        (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
        (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
        (φ : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F') (U : S.Etale)
        (z : (abelianHigherDirectImageRawPresheaf h p F).obj (op U)),
        (abelianHigherDirectImageMap a h h' w p F F' φ).hom.app (op U)
          ((toSheafify S.smallEtaleTopology (abelianHigherDirectImageRawPresheaf h p F) ≫
            (e h F).hom.hom).app (op U) z) =
          (toSheafify S.smallEtaleTopology (abelianHigherDirectImageRawPresheaf h' p F') ≫
            (e h' F').hom.hom).app (op U)
              (abelianHigherDirectImageRawPullback a h h' w p F F' φ U z) := by sorry

end AlgebraicGeometry.Etale
