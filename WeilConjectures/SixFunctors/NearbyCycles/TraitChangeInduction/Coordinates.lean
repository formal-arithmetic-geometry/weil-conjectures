/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLineConstructible
public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedPoints

/-!

# Non-closed points have a generic coordinate

Let `K` be a field and `e : Z ⟶ 𝔸(ι; K)` an immersion, `ι` finite. A point of `Z` which is not
closed has a coordinate `Z ⟶ 𝔸¹_K` sending it to the generic point of the affine line
(`AlgebraicGeometry.AffineSpace.exists_isGenericPoint_reindex_of_not_isClosed`): this is how the
slice step of Deligne's induction (SGA 4½, [Th. finitude], 3.7) reaches every non-closed point of
the special fibre.

-/

@[expose] public section

universe u

open CategoryTheory Set

namespace AlgebraicGeometry.AffineSpace

end AlgebraicGeometry.AffineSpace
