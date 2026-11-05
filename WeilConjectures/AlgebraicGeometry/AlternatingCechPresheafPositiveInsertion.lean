/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CechCapPresheafLocalIso

/-! # Positive-degree signed insertion before sheafification

Source: Stacks Project, Tags 02FU and 01FM.
(blueprint: lem-pc-s3-alternating-cech-presheaf-positive-insertion).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

namespace CechInsertion
noncomputable section

/- Insert an absent index into the finite ordered range of a tuple.
Source: Stacks 01FM, ordered indices; 02FU, insertion. -/

/- The sign exponent is the number of tuple entries strictly before the inserted index.
Source: Stacks 01FM, ordered signs; 02FU, insertion. -/

/- One signed insertion coordinate, zero if the inserted index is already present.
Source: Stacks 02FU, increasing-tuple adaptation of 01FM. -/

/- Assemble signed insertion coordinates by the finite product comparison.
Source: Stacks 02FU, increasing-tuple adaptation of 01FM. -/

/- The coordinate of insertion followed by the differential: its signed face sum.
Source: Stacks 02FU, ordered deletion calculation as in 01FM. -/

end
end CechInsertion

/- For a tuple already containing the inserted index, exactly its deletion survives.
Source: Stacks 02FU, insertion computation; increasing tuples as in 01FM.

Proof: Write i=a b. Every face other than b still contains i, so its insertion
coordinate is zero. The b face omits i; inserting it recovers a, in position b.
The two signs multiply to one. Restriction through the deleted face followed by
intersection with U i is just the cap unit on the a-coordinate. The other
insertion term is zero because a itself contains i. -/

/- Paired noncentral faces cancel on a tuple omitting the inserted index.
Source: Stacks 02FU, the displayed dh+hd computation; increasing tuples as in 01FM.

Proof: Enlarge a by inserting i in its unique position b. In d followed by
insertion at a, the face deleting b is the restriction of the a-coordinate,
since its two signs multiply to one. Each other face, indexed by b.succAbove j,
is the sorted insertion into the j-face of a. Its pivot position is j.predAbove b.
The two deletion orders agree by the succAbove identity. If j<b, the two sign
exponents are j+b-1 and j+b; otherwise they are j+b and j+b+1, so the terms are
negatives. The restrictions compose to the same map to G on V intersect U i
intersect the intersection of a. Summing the paired negatives leaves precisely
the cap unit of the a-coordinate. Empty intersections do not alter the argument;
if the tuple type is empty there is no coordinate to check. No covering condition
or sheafification is used. -/

end AlgebraicGeometry
