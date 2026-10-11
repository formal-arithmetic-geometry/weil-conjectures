import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Ampleness on a Noetherian reduction

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS
(blueprint: lem-sc-ample-on-reduction-noetherian).

The invertibility of the pullback `i^*L` (the node's parenthetical) is the first clause of
the landed `Scheme.Modules.invertible_pullback_tensor`
(lem-weil-pbc-invertible-pullback-tensor); it is not restated here.
-/

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/-- Ampleness of an invertible module is unchanged on a Noetherian closed subscheme
with the same underlying topological space.
Source: Stacks Project, Cohomology of Schemes, Lemma 09MS
(blueprint: lem-sc-ample-on-reduction-noetherian).
Proof: the forward implication follows from affine pullback along a closed immersion.
For the converse, the ideal sheaf of the immersion is nilpotent; form the chain of
closed subschemes cut out by its powers. Consecutive immersions have square-zero ideal
sheaves, so ampleness lifts inductively by the square-zero thickening lemma.
-/
theorem isAmple_iff_of_isClosedImmersion_of_isHomeomorph {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
    [CompactSpace Z] [CompactSpace X]
    (hi : IsHomeomorph i.base) (L : X.Modules) [L.IsInvertible] :
    letI : ((Scheme.Modules.tensorPullback i).obj L).IsInvertible :=
      ((Scheme.Modules.invertible_pullback_tensor i).1 L).2
    AlgebraicGeometry.Scheme.Modules.IsAmple Z ((Scheme.Modules.tensorPullback i).obj L) ↔
      AlgebraicGeometry.Scheme.Modules.IsAmple X L := by
  sorry

end AlgebraicGeometry
