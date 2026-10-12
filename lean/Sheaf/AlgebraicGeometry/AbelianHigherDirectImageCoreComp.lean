/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageMap

/-! # Canonical-coefficient composition for abelian higher direct images

Source: Stacks Project, Tag 09Z1, canonical comparison maps.
(blueprint: lem-sbc-abelian-higher-direct-image-core-comp).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Composition with canonical pullback coefficients, before inserting arbitrary
coefficient morphisms. Source: Stacks Project, Tag 09Z1, canonical comparison maps.
(blueprint: lem-sbc-abelian-higher-direct-image-core-comp).

Proof: Expand the two maps as the derived adjunction units followed by direct
images of pullback comparisons and counits, and the single-complex comparisons.
Transpose along the h'' derived adjunction. Naturality moves the intermediate
unit past the first pulled-back counit. The h' triangle identity cancels the
intermediate counit and unit. Associativity of the inverse-image comparison
identifies the remaining counit composite with that for b followed by a.
The composition comparison for exact functors commutes with single complexes:
on their degree-zero representatives this is the ordinary pullback composition
comparison, and localization preserves this equality. Apply degree-p homology,
which preserves composition. The proofs of the structure-map equalities agree
by proof irrelevance. This works for identity scheme maps, zero sheaves, and
p = 0, with no geometric hypotheses. -/
theorem abelianHigherDirectImage_core_comp {S Y Y' Y'' : Scheme.{v}}
    (a : Y' ⟶ Y) (b : Y'' ⟶ Y') (h : Y ⟶ S) (h' : Y' ⟶ S) (h'' : Y'' ⟶ S)
    (wa : a ≫ h = h') (wb : b ≫ h' = h'') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    abelianHigherDirectImageMap (b ≫ a) h h''
        (by rw [Category.assoc, wa, wb]) p F
        (((b)^*[AddCommGrpCat.{v + 1}]).obj
          (((a)^*[AddCommGrpCat.{v + 1}]).obj F))
        ((upperStarComp AddCommGrpCat.{v + 1} b a).hom.app F) =
      abelianHigherDirectImageMap a h h' wa p F
          (((a)^*[AddCommGrpCat.{v + 1}]).obj F) (𝟙 _) ≫
        abelianHigherDirectImageMap b h' h'' wb p
          (((a)^*[AddCommGrpCat.{v + 1}]).obj F)
          (((b)^*[AddCommGrpCat.{v + 1}]).obj
            (((a)^*[AddCommGrpCat.{v + 1}]).obj F)) (𝟙 _) := by sorry

end AlgebraicGeometry.Etale
