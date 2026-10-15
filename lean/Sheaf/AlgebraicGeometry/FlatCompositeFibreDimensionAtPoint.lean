import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Pointwise fibre dimension is additive for a flat first morphism

Source: literature/stacks-project/morphisms.tex, Tag 02JS
(blueprint: lem-sbc-flat-composite-fibre-dimension-at-point)
-/

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 02JS (blueprint: lem-sbc-flat-composite-fibre-dimension-at-point).

Proof:
1. Put x = a(u) and s = f(x). By `lem-sbc-composite-fibre-local-models`, set
   A = O_{X_s,x}, B = O_{U_s,u}, and C = O_{U_x,u}. These are Noetherian local
   rings, A → B is local and flat by flatness of a at u, and B / m_A B ≅ C.
   The same lemma gives finite-type affine neighbourhoods in the three fibres
   with the required stalk and residue-field identifications. This uses no
   Noetherian hypothesis on S.
2. Apply `lem-weil-pbc-flat-height-formula` (Stacks 00ON) at the maximal ideal
   of B. Its contraction is m_A, and localizing either local ring at its
   maximal ideal changes nothing. Thus dim B = dim A + dim C.
3. Apply `lem-kun-dimension-formula` to the three affine neighbourhoods and
   `lem-weil-pbc-dimension-at-point-open-subspace` to pass to the whole fibres.
   This gives dim_u U_s = dim B + trdeg_{κ(s)} κ(u),
   dim_u U_x = dim C + trdeg_{κ(x)} κ(u), and
   dim_x X_s = dim A + trdeg_{κ(s)} κ(x). By `lem-kun-dimension-finite-type`,
   each neighbourhood has finite dimension, so its dimension at the point
   and the nonnegative terms in these formulas are finite.
4. Apply `lem-sbc-transcendence-degree-tower` to κ(s) → κ(x) → κ(u).
   Substitute trdeg_{κ(s)} κ(u) = trdeg_{κ(x)} κ(u) + trdeg_{κ(s)} κ(x)
   and the equality from step 2 into step 3. Rearranging the finite sums gives
   dim_u U_s = (dim C + trdeg_{κ(x)} κ(u)) +
   (dim A + trdeg_{κ(s)} κ(x)) = dim_u U_x + dim_x X_s.
-/
theorem flat_composite_fibre_dimension_at_point
    {U X S : Scheme.{u}} (a : U ⟶ X) (f : X ⟶ S) (u : U)
    [LocallyOfFiniteType a] [LocallyOfFiniteType f]
    (hflat : (a.stalkMap u).hom.Flat) :
    topologicalKrullDimAt ((a ≫ f).asFiber u) =
      topologicalKrullDimAt (a.asFiber u) + topologicalKrullDimAt (f.asFiber (a u)) := by
  sorry

end AlgebraicGeometry
