module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Sheaf.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen

/-!
# Lower bound for dimensions of fibres of an irreducible finite-type scheme

Source: Stacks Project, varieties.tex, Tag 0B2L
(blueprint: lem-zl-irreducible-fibre-dimension-lower-bound).
-/


@[expose] public section

set_option autoImplicit false

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Stacks Project, varieties.tex, Tag 0B2L, parts (2)(a) and (2)(b)
(blueprint: lem-zl-irreducible-fibre-dimension-lower-bound).
If `X` is irreducible and of finite type
over a field and `f : X ⟶ Y` is a morphism over that field, every local fibre dimension is
bounded below by the dimension difference, and this bound is attained on a dense open subset.
The difference is expressed by its natural-number representative, since
`WithBot ℕ∞` has no subtraction operation.

Proof (the eight steps of the node, following Tag 0B2L):
1. A field is Noetherian, and its spectrum is quasi-compact. Apply
   `lem-weil-pbc-finite-type-over-noetherian` to make `X` Noetherian. The minimal-closed-set
   theorem `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` gives the descending-chain
   condition. Then `lem-sfb-noetherian-space-compact-subsets` makes every subset compact.
2. The composite of `f` with the structure map of `Y` is the structure map of `X`.
   Clause (f) of `lem-weil-pbc-proper-fp-permanence` makes `f` locally of finite type.
   Step 1 makes inverse images of affine opens compact, so `f` is finite type
   (`def-weil-finite-type-morphism`). Base change by `lem-sfb-finite-type-composition-base-change`
   makes every fibre finite type over its residue field. Its dimension is finite by
   `lem-kun-dimension-finite-type`.
3. Irreducibility includes nonemptiness. Choose the generic point `η` using
   `lem-weil-pbc-scheme-sober`, and put `ξ = f η`. The inverse image of the closure of `ξ`
   is closed and contains `η`, so it is all of `X`. As `ξ` belongs to the image,
   `Z = closure (range f)` is the closure of `ξ`, with generic point `ξ`.
   Every nonempty open of `X` contains `η`, since its closed complement cannot contain `η`.
4. Apply `lem-sc-closed-irreducible-dimension-trdeg` to the whole of `X` and to `Z` in `Y`.
   Their dimensions are the transcendence degrees of the generic residue fields over `k`.
   They are finite by `lem-kun-dimension-finite-type` and monotonicity for a closed subspace.
   The residue-field tower and `lem-kun-transcendence-degree-tower` therefore give a natural
   number `r = trdeg κ(ξ) κ(η)` and `dim X = dim Z + r`, without infinite subtraction.
5. The fibre homeomorphism in `def-pc-scheme-fibre` identifies `F = X_ξ` with the subspace
   of points mapping to `ξ`. It contains `η` as a generic point and is irreducible.
   By `lem-weil-pbc-fibre-product-point-residue-field`, its residue field at that point
   identifies with `κ(η)` compatibly with `κ(ξ)`: the point tensor ring is
   `κ(η) ⊗[κ(ξ)] κ(ξ)`, with isomorphism `a ⊗ b ↦ a * f♯(b)` and inverse `a ↦ a ⊗ 1`.
   This ring is a field, so the kernel prime is zero and the residue field is the same field.
6. Apply `lem-sc-closed-irreducible-dimension-trdeg` to the finite type irreducible fibre
   `F`. Step 5 gives `dim F = r`. By `lem-sc-dimension-locally-algebraic`, its local
   dimension at every point, including the point corresponding to `η`, is also `r`.
7. For any `x`, the minimum in `def-kun-topological-dimension-at-point` for its nonempty
   fibre is a finite nonnegative integer `n`: it is bounded by the finite global fibre
   dimension from step 2. By `lem-weil-pbc-local-fibre-dimension-open`, the locus of local
   fibre dimension at most `n` is open and contains `x`. It therefore contains `η` by
   step 3. Evaluating there gives `r ≤ n`, proving the pointwise lower bound.
8. Apply the same openness theorem at `r`. This open locus contains `η` by step 6, hence
   is dense. The lower bound from step 7 identifies it with the entire equality locus. -/
theorem irreducible_fibre_dimension_lower_bound
    (k : Type u) [Field k]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IrreducibleSpace X]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    ∃ r : ℕ,
      topologicalKrullDim X =
        topologicalKrullDim (closure (Set.range f.base) : Set Y) +
          (r : WithBot ℕ∞) ∧
      (∀ x : X, (r : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.asFiber x)) ∧
      Dense {x : X | topologicalKrullDimAt (f.asFiber x) = (r : WithBot ℕ∞)} ∧
      IsOpen {x : X | topologicalKrullDimAt (f.asFiber x) = (r : WithBot ℕ∞)} := by
  sorry

end AlgebraicGeometry

end
