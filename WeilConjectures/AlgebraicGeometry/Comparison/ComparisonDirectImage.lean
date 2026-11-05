/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp

/-!
# The canonical comparison for bounded below direct images

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
prop-weil-pbc-comparison-direct-image; Stacks Project, Tag 099R
(blueprint: prop-weil-pbc-comparison-direct-image).

The comparison is the existing derived base-change transformation of the canonical
underived mate. The three statements give invertibility, identity compatibility and
composition compatibility. Naturality in the complex is built into the transformation.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
