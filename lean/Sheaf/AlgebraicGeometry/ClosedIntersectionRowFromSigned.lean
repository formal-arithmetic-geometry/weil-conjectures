/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.ClosedIntersectionAugmentedRow
public import Sheaf.AlgebraicGeometry.ClosedRestrictionSignedRefinements

/-! The bridge from signed closed rows to the augmented finite-subset presentation. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtaleTensorComparison

namespace AlgebraicGeometry.ClosedIntersection

/-- Insert the support augmentation in degree -1 and reindex the ordered terms by
finite subsets. This does not assert exactness, locality, or a contraction.

Source: Stacks Project, Tags 09AH and 01FG; step 2 of
lem-sfb-closed-intersection-vertex-contraction.
(blueprint: lem-sfb-closed-intersection-row-from-signed).

Proof: Use the given row in nonnegative degrees, its support object E_Z in degree
-1, and zero below -1. The map from degree -1 to zero is its given augmentation;
all other differentials are the given ones or zero. The chain-map equation for
alpha says that augmentation followed by d from zero to one is zero. The other
squares vanish by the row's differential-square equation or because an object is
zero. Apply this construction to morphisms using the given natural augmentation;
this defines an additive functor.
The empty subset is the unique subset of augmented degree -1, so its product is
canonically E_Z. In nonnegative degree p, send an increasing (p+1)-tuple to its
image subset. Its inverse lists a subset in increasing order. These are inverse
bijections and induce the required product isomorphisms. Outside the finite
range both indexing types are empty and both terms are zero.
For nonempty source and target indices use the given restriction when the source
is contained in the target, and zero otherwise. For the empty source and nonempty
target use fromSupport; for two empty indices use the identity. A nonempty source
and empty target has zero map. The unit equations follow respectively from
restriction_unit, fromSupport_unit and the identity equation. The matrix formula
in nonnegative degrees is the original differential formula under the bijection:
the number of vertices smaller than the deleted vertex is its position. At the
augmentation it is exactly augment_components and the sign is one. In all other
degrees the source or target product is zero. Thus all fields of Row hold,
naturally in the module, with precisely the prescribed units and signs. -/
theorem row_from_signed {X Z : Scheme.{u}} {i : Z ⟶ X}
    (F : SignedClosedFamily i) (A : Rings X) (S : SignedClosedRow i F A) :
    Nonempty (Row i F.members A) := by sorry

end AlgebraicGeometry.ClosedIntersection
