module

public import Mathlib.Analysis.Convex.Side
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.GroupTheory.CosetCover

/-!
# Generic broken lines through finite affine hyperplane arrangements

Source: Milne, Algebraic Groups, Appendix C.8--C.10 and C.19--C.22, printed pp.609--612,
for chamber terminology. The finite-affine-arrangement argument is an agent supporting lemma,
not a theorem quoted from Milne (blueprint: lem-sfb-arrangement-generic-broken-line).
-/

@[expose] public section

universe u

namespace AffineSubspace

/-- A finite affine hyperplane arrangement has dense regular locus, and regular points in
an open convex set admit a generic two-segment path and its ordered chamber gallery.

Source: Milne, Algebraic Groups, Appendix C.8--C.10 and C.19--C.22, printed pp.609--612,
chamber geometry; agent supporting argument, not a quoted assertion of Milne
(blueprint: lem-sfb-arrangement-generic-broken-line).

The hyperplanes are nonempty affine subspaces with codimension-one directions. The regular
locus is written inline as the points lying on none of them. The gallery has `n` crossings,
`n + 1` components, and `n + 2` division times, including the endpoints. Between division times
the actual concatenated path lies in the indicated component. At an internal division time
it lies on exactly one wall, in the closures of both adjacent components; these components
are on opposite strict sides of that wall and the same strict side of every other wall.
Thus `n = 0` is a one-component gallery, and constant segments are permitted.

Proof:
1. Choose a nonzero linear coordinate functional for the direction of each hyperplane and
   translate it to an affine functional vanishing on that hyperplane. Continuity follows from
   `LinearMap.continuous_of_finiteDimensional`
   (lem-sfb-finite-dimensional-linear-map-continuous). In dimension zero no such direction
   exists, so the arrangement is empty and every path under consideration is constant.
2. Apply `Subspace.biUnion_ne_univ_of_top_notMem` (lem-pc-finite-linear-avoidance) to the kernels
   of the linear functionals. A line in the resulting direction through a point of a nonempty
   open set stays in that set for small parameters; each wall excludes only one parameter.
   Avoid finitely many parameters to obtain density.
3. For each intersecting pair of distinct walls and each endpoint `p`, form the affine function
   `f_H(p) * f_K - f_K(p) * f_H`. Its linear part is nonzero: otherwise the two original
   functionals, translated through a common point, would be proportional and the walls equal.
4. Apply finite linear avoidance to these linear parts and the original ones. On a sufficiently
   short line inside the open set exclude the finitely many zeros of all affine functions.
   Its chosen point `z` is regular. If a segment from an endpoint to `z` met two walls, the two
   affine zero equations would force one of the auxiliary functions to vanish at `z`.
   Convexity keeps both segments inside the given set.
5. On each leg each wall functional is an affine function of the parameter with nonzero
   endpoint values. It has at most one zero, necessarily interior, with opposite endpoint
   signs. A constant leg has no zero.
6. Nonempty strict sign regions are convex and hence connected by `Convex.isConnected`
   (lem-sfb-convex-set-connected). A connected subset of the regular locus has a constant sign
   for each functional, since opposite signs give a disjoint relatively open partition.
   Thus these regions are exactly its maximal connected subsets.
7. Sort the finitely many crossing times of the concatenated path. There is no crossing at
   either endpoint or at the bend, and no simultaneous crossing of different walls. Each
   interval between crossings lies in one sign region. At a crossing just one sign changes;
   continuity keeps every other sign fixed on a neighborhood. This gives the stated gallery,
   its closure incidences and its strict-side assertions. With no crossings use times 0 and 1.
-/
theorem arrangement_generic_broken_line
    (E : Type u) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (ℋ : Finset (AffineSubspace ℝ E))
    (hℋ : ∀ H ∈ ℋ, (H : Set E).Nonempty ∧
      Module.finrank ℝ H.direction + 1 = Module.finrank ℝ E) :
    (∀ O : Set E, IsOpen O → O.Nonempty → ∃ q ∈ O, ∀ H ∈ ℋ, q ∉ H) ∧
    (∀ U : Set E, U.Nonempty → IsOpen U → Convex ℝ U →
      ∀ x ∈ U, ∀ y ∈ U, (∀ H ∈ ℋ, x ∉ H) → (∀ H ∈ ℋ, y ∉ H) →
      ∃ (z : E) (γ : Path x y), z ∈ U ∧ (∀ H ∈ ℋ, z ∉ H) ∧
        γ = (Path.segment x z).trans (Path.segment z y) ∧
        segment ℝ x z ∪ segment ℝ z y ⊆ U ∧
        (∀ H ∈ ℋ, ∀ K ∈ ℋ, H ≠ K →
          Disjoint (segment ℝ x z ∪ segment ℝ z y) ((H : Set E) ∩ (K : Set E))) ∧
        (∀ a b : E, ((a = x ∧ b = z) ∨ (a = z ∧ b = y)) →
          ∀ H ∈ ℋ, ∀ t ∈ Set.Icc (0 : ℝ) 1, AffineMap.lineMap a b t ∈ H →
            t ∈ Set.Ioo (0 : ℝ) 1 ∧ H.SOppSide a b ∧
            ∀ s ∈ Set.Icc (0 : ℝ) 1, AffineMap.lineMap a b s ∈ H → s = t) ∧
        ∃ (n : ℕ) (t : Fin (n + 2) → ℝ) (C : Fin (n + 1) → Set E),
          StrictMono t ∧ t 0 = 0 ∧ t (Fin.last (n + 1)) = 1 ∧
          C 0 = connectedComponentIn {q : E | ∀ H ∈ ℋ, q ∉ H} x ∧
          C (Fin.last n) = connectedComponentIn {q : E | ∀ H ∈ ℋ, q ∉ H} y ∧
          (∀ i, ∃ p : E, (∀ H ∈ ℋ, p ∉ H) ∧
            C i = connectedComponentIn {q : E | ∀ H ∈ ℋ, q ∉ H} p) ∧
          (∀ i : Fin (n + 1), ∀ s ∈ Set.Ioo (t i.castSucc) (t i.succ),
            γ.extend s ∈ C i) ∧
          (∀ i : Fin n, ∃ H ∈ ℋ,
            γ.extend (t i.succ.castSucc) ∈ H ∧
            (∀ K ∈ ℋ, K ≠ H → γ.extend (t i.succ.castSucc) ∉ K) ∧
            γ.extend (t i.succ.castSucc) ∈ closure (C i.castSucc) ∧
            γ.extend (t i.succ.castSucc) ∈ closure (C i.succ) ∧
            (∀ a ∈ C i.castSucc, ∀ b ∈ C i.succ,
              H.SOppSide a b ∧ ∀ K ∈ ℋ, K ≠ H → K.SSameSide a b))) ∧
    (Module.finrank ℝ E = 0 → ℋ = ∅) := by
  sorry

end AffineSubspace
