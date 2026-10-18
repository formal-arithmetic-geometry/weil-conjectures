/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import Sheaf.Paper.ProperOpenRefinementAdjointProjection
import Sheaf.Paper.UnboundedProperOpenInterchange

/-!
# Coherence of the specified compact-support graph map

Source: SGA 4 XVII 5.2.2, 6.2.11; Stacks Project Tags 03S6, 0F7B and 0F7C
(blueprint: lem-asd-compact-support-graph-coherence).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Base change, proper refinement and identity for the specified graph comparison.
Source: SGA 4 XVII 5.2.2, 6.2.11; Stacks Project Tags 03S6, 0F7B and 0F7C.
(blueprint: lem-asd-compact-support-graph-coherence).

Proof:
1. For a base-change square pull back the clopen graph and its projection. On the
new graph both routes are identity, and on its complement both are zero. The
specified beta maps are conjugates of direct-image exchange; mate pasting identifies
the composite restrictions. This proves equality of the sheaf transposes.
2. Descend degreewise to the homotopy category, compose with the right-derived units,
and use localization full faithfulness. Transposition under the proper adjunction
identifies this equality with the actual proper/open exchange square. Cancel the
invertible derived graph maps to obtain the stated square for their inverses.
3. For a proper refinement apply the proper/open interchange to its two open
immersions. Its adjunct is projection to the coarser clopen graph. On composing
proper direct images, the two graph transposes agree, because each retains exactly
the original U-component. The canonical derived direct-image composition comparison
then gives the refinement equation by cancellation.
4. For the identity with its proper identity compactification the graph projection
is identity. The derived unit of the identity direct image is the inverse of its
exact-derived comparison; the canonical direct-image identity and the right unitor
therefore give precisely identityEtaleCompactSupportComparison.
These equalities hold on all unbounded complexes, with empty fibres allowed. -/
theorem etaleCompactSupportGraph_coherence
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    EtaleCompactSupportCoherence A (canonicalEtaleCompactSupportCore A) := by
  sorry

end AlgebraicGeometry.Etale
