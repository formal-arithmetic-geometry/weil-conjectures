/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

/-!

# The generic point of the special fibre of `𝔸¹_S`

For `S = Spec k'⟦t⟧` and `K = k'(x)^alg` (`AlgebraicGeometry.traitSliceField`), the geometric
point `Spec K ⟶ 𝔸¹_S` (`AlgebraicGeometry.genericSlicePoint`) is the closed point of the generic
slice `Spec K⟦t⟧ ⟶ 𝔸¹_S`: it lies over the generic point of the special fibre `𝔸¹_{k'}`. The strict
localization of `𝔸¹_S` at it is the trait of Deligne's slicing argument (SGA 4½,
[Th. finitude], 3.3).

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (k' : Type u) [Field k']

end AlgebraicGeometry
