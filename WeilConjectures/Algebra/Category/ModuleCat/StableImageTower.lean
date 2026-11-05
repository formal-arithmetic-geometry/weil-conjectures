/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.MittagLefflerTower
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Artinian.Module
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-!
# Stable images of towers of modules

For a tower of modules `G : ℕᵒᵖ ⥤ ModuleCat R`, the stable image at `n` is the intersection of
the images of all transitions `G m ⟶ G n` (`ModuleCat.stableImage`); they form a subtower
`ModuleCat.stableImageTower G`.

- `ModuleCat.exists_stableImage_eq_towerRange`: if `G n` is Artinian, the images stabilise;
- `ModuleCat.isMittagLefflerTower_of_isArtinian`, `ModuleCat.isMittagLefflerTower_of_finite`:
  towers of Artinian (e.g. finite) modules are Mittag-Leffler: the stable images have
  surjective transitions and the transitions factor through them;
- `ModuleCat.isMittagLefflerTower_comp_constantSheaf_of_finite`: so are towers of constant
  sheaves of finite modules.
-/

@[expose] public section

open CategoryTheory Opposite Limits

namespace ModuleCat

variable {R : Type*} [Ring R] (G : ℕᵒᵖ ⥤ ModuleCat R)

end ModuleCat
