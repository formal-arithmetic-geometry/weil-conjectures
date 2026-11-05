/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleUniversalNormalization
import all WeilConjectures.AlgebraicGeometry.Source.SourceIsomorphismNormalizedPresheafEvaluation
import WeilConjectures.CategoryTheory.Constant.ConstantDerivedNormalizationUniversalSupplement
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # Sourcewise universality for constant normalization arrows

Source: Stacks Project, Tags 06YY and 03ED.
(blueprint: lem-weil-pbc-etale-constant-arrow-universal-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
section ConstantSlice
variable {C : Type (t + 1)} [Category.{t} C] [EssentiallySmall.{t + 1} C]
    (J : GrothendieckTopology C) (U : C)
    {R S : Type (t + 1)} [CommRing R] [CommRing S]

end ConstantSlice
end CategoryTheory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
