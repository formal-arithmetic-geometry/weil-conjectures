/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Derived category of modules on the small pro-etale site

Source: the Weil conjectures blueprint, `def-weil-pbc-proetale-site`, order 662
(blueprint: def-weil-pbc-proetale-site).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- (blueprint: def-weil-pbc-proetale-site) For a scheme `Y` and a commutative ring `A`,
the small pro-etale site is `Y.ProEt` with `ProEt.topology Y`: its objects are weakly
etale schemes over `Y`, and its covers are the pro-etale (fpqc) covering families.
The constant ring sheaf `A_Y` is the sheafification of the constant presheaf.
The category of sheaves of `A_Y`-modules is `SheafOfModules`; its derived category
is the localization of cochain complexes at quasi-isomorphisms (`HasDerivedCategory.standard`);
as an `abbrev` it carries the category and triangulated structure of `DerivedCategory`.

Source: the Weil conjectures blueprint, `def-weil-pbc-proetale-site`, order 662;
Stacks Project, Tag 098K (the small site) and Tag 05RU (the derived category). -/
noncomputable abbrev proEtaleDerivedCategory (Y : Scheme.{u})
    (A : Type u) [CommRing A] : Type _ :=
  @DerivedCategory
    (SheafOfModules.{u + 1}
      ((constantSheaf (ProEt.topology Y) RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} A))))
    _ _ (HasDerivedCategory.standard _)

end AlgebraicGeometry.Scheme
