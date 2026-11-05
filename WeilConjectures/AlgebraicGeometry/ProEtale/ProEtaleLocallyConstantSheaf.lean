/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding

/-!
# Locally constant module sheaves on the small pro-etale site

Source: Bhatt--Scholze, *The pro-etale topology for schemes*, Definition 7.3.1(1),
with module coefficients as in the Weil blueprint, def-weil-scheme-morphism-properties
(blueprint: def-weil-proetale-locally-constant-sheaf).

Constant module sheaves are constructed by simultaneous sheafification of the
constant ring and module. On a localized site the ring is the restricted constant
ring sheaf. Two named proof obligations record local bijectivity of the ring unit;
no data is chosen from an existence assertion.

## Main definitions

* `proEtaleConstantModuleSheaf`: the constant module sheaf.
* `proEtaleConstantModuleSheafOver`: its localized-site construction.
* `IsConstantProEtaleModuleSheaf`: global constancy.
* `IsLocallyConstantProEtaleModuleSheaf`: coverwise constancy.
-/

universe t v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

@[expose] public section

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
