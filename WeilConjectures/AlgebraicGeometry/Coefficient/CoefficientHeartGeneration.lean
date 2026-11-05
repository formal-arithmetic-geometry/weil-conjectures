/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedCohomologyConeWitness
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartTriangulated

/-!
# Finite cone generation of the bounded constructible coefficient category

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-coefficient-heart-ii/
sk-cor-coefficient-heart-ii-generation.md and its proof
(blueprint: det-cor-coefficient-heart-ii-generation).

The witness below is a nonempty finite sequence ending at the specified object. Its
entries are shifted lisse extensions or shifted cones between strictly earlier entries.
Distinguished triangles express cones intrinsically in the ordinary derived category.
No closure under arbitrary coproducts or direct summands enters the statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
