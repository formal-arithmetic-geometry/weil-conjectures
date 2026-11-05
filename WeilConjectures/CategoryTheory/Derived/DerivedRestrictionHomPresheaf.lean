/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedMorphismPresheaf
public import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Restriction of coefficients on local derived Hom presheaves

Source: Stacks Project, Tags 03DA and 098K, restriction and localization of coefficients.
(blueprint: def-weil-pbc-restriction-hom-presheaf).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {B B' : Type (u + 1)}
  [CommRing B] [CommRing B'] (φ : B →+* B')

end CategoryTheory
