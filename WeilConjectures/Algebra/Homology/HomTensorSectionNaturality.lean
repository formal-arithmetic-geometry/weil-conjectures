/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorComparisonNaturality
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Naturality of the canonical map to the sheaf tensor product

## References

* [Stacks Project, Tag 03CY](https://stacks.math.columbia.edu/tag/03CY)
* [Stacks Project, Tag 03EK](https://stacks.math.columbia.edu/tag/03EK)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from the presheaf tensor to the sheaf tensor is natural. -/
theorem homTensorSectionMap_natural {A A' B B' : Mod}
    (f : A' ⟶ A) (g : B' ⟶ B) :
    letI := SheafOfModules.monoidalCategory R
    homTensorSectionMap R A' B' ≫ (f ⊗ₘ g).val =
      (f.val ⊗ₘ g.val) ≫ homTensorSectionMap R A B := by
  let := SheafOfModules.monoidalCategory R
  let S := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have hc := homTensorComparison_natural R f g
  have hi : (SheafOfModules.tensorObjIsoSheafification A' B').inv ≫ (f ⊗ₘ g) =
      S.map (f.val ⊗ₘ g.val) ≫
        (SheafOfModules.tensorObjIsoSheafification A B).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hv := congrArg SheafOfModules.Hom.val hi
  change (SheafOfModules.tensorObjIsoSheafification A' B').inv.val ≫ (f ⊗ₘ g).val =
    (S.map (f.val ⊗ₘ g.val)).val ≫
      (SheafOfModules.tensorObjIsoSheafification A B).inv.val at hv
  have hn := adj.unit.naturality (f.val ⊗ₘ g.val)
  change (f.val ⊗ₘ g.val) ≫ adj.unit.app (A.val ⊗ B.val) =
    adj.unit.app (A'.val ⊗ B'.val) ≫ (S.map (f.val ⊗ₘ g.val)).val at hn
  unfold homTensorSectionMap
  erw [Category.assoc, hv, ← Category.assoc, ← hn]
  rfl

end CategoryTheory
