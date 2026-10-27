module

public import Sheaf.AlgebraicGeometry.IntersectionNumber
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.AlgebraicGeometry.AmplePullback
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import Sheaf.AlgebraicGeometry.TopDimensionalReductionIntersection
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier
import Sheaf.AlgebraicGeometry.IntersectionEffectiveCartier

/-! # Positivity of mixed ample intersection numbers

Source: Stacks Project, Varieties, Tag 0BEV, lemma-ample-positive, with the closed
subscheme equal to the ambient scheme
(blueprint: lem-sfb-ample-mixed-intersection-positive).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The mixed intersection number of `d` ample invertible modules on a nonempty proper
`d`-dimensional scheme is strictly positive. The modules can be different, and the scheme
can be nonreduced, reducible, nonequidimensional, or singular.

Source: Stacks Project, Varieties, Tag 0BEV, lemma-ample-positive, specialized to `Z = X`
(blueprint: lem-sfb-ample-mixed-intersection-positive).

Proof:
1. First establish restriction to a nonempty closed subscheme. Closed immersions are
   proper (`lem-weil-pbc-closed-immersion-proper`) and affine
   (`def-weil-closed-immersion`); their pullbacks preserve ampleness
   (`lem-weil-pbc-pullback-ample-invertible`). The projection formula and closed-pushforward
   cohomology comparison (`lem-pc-closed-immersion-coherent-cohomology`) identify the
   Euler characteristics (`def-pc-euler-characteristic`) of every twist, hence their
   intersection coefficients (`def-sc-intersection-number`).
2. Induct simultaneously on the dimension `e` of every nonempty proper scheme. For
   `e = 0`, the empty intersection is the Euler characteristic of the structure sheaf.
   By `lem-pc-chi-zero-dim-support` it is the dimension of global sections, which is
   positive: the unit section has nonzero germ at any point.
3. For `e > 0`, `lem-sc-top-dimensional-reduction-intersection` expresses the number as
   a sum over the reduced integral top-dimensional components, with positive generic
   lengths. There is at least one such component. Step 1 restricts the ample modules
   and identifies the intersection numbers. It suffices to treat an integral scheme.
4. By `def-weil-pbc-ample-invertible-module`, a positive tensor power of the first
   module has a nonzero section whose nonvanishing open is affine. By
   `lem-sfb-top-intersection-multilinear`, replacing that module by its r-th power
   multiplies the intersection by the positive integer r; the other modules stay fixed.
5. The zero scheme (`def-pc-zero-scheme`) is nonempty: otherwise the whole scheme is
   affine, hence finite over the field by `lem-sc-proper-affine-finite-general`.
   By `lem-weil-pbc-finite-over-field-affine-finite-dim`, its coordinate algebra is
   finite-dimensional. Every prime quotient is then a field, contradicting `e > 0`.
6. By `lem-pc-nonzero-section-integral-cartier`, this zero scheme is an effective
   Cartier divisor. By `lem-sc-intersection-effective-cartier`, it is proper of
   dimension `e - 1`, and its intersection with the remaining modules equals the
   powered intersection on the ambient scheme. Step 1 gives ample restrictions.
7. Apply the induction hypothesis to this nonempty divisor, including the empty list
   when `e = 1`. Divide by the positive power from Step 4 and assemble the positive
   component contributions from Step 3. Specialize to dimension d and ambient scheme X.
-/
theorem intersectionNumber_pos_of_isAmple
    (k : Type u) [Field k] (X : Scheme.{u}) [Nonempty X]
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (d : ℕ) (_hd : 1 ≤ d)
    (hdim : topologicalKrullDim X = ((d : ℕ∞) : WithBot ℕ∞))
    (L : Fin d → X.Modules) [∀ j : Fin d, (L j).IsInvertible]
    (_hL : ∀ j : Fin d, IsAmple X (L j)) :
    0 < intersectionNumber k X X (𝟙 X) d hdim L := by
  sorry

end AlgebraicGeometry.Scheme.Modules
