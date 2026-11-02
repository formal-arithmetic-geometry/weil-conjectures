/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound

/-!
# Openness of the bounded local fibre dimension locus

Source: Stacks Project, Morphisms, Tag 02FZ, lemma-openness-bounded-dimension-fibres
(blueprint: lem-weil-pbc-local-fibre-dimension-open).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a locally finite type morphism, the points with local fibre dimension at most `n`
form an open subset of the source. The point `f.asFiber x` is the unique point of
`f.fiber (f x)` mapping to `x`. No properness, quasi-compactness, Noetherian,
finite-presentation, or flatness hypothesis is imposed.

Source: Stacks Project, Morphisms, Tag 02FZ, lemma-openness-bounded-dimension-fibres
(blueprint: lem-weil-pbc-local-fibre-dimension-open).

Proof: fix a point `x` in the locus. Choose an affine open of the base containing `f x`
and an affine open `W` of its inverse image containing `x`, on which the coordinate
ring map is finite type, using the affine-cover characterization of locally finite type
(def-weil-finite-type-morphism, def-weil-affine-spectrum). The fibre homeomorphism
(def-pc-scheme-fibre) identifies the restricted fibre with an open subspace of the original
fibre. Local dimension is unchanged on this open subspace
(lem-weil-pbc-dimension-at-point-open-subspace). Compare with the coordinate-ring fibre
using `affine_coordinate_fibre_dimension_eq`
(lem-sbc-affine-coordinate-fibre-dimension); swapping tensor factors preserves the
specified prime and its local topological dimension. The local dimension at `x` is a
nonnegative integer `d` at most `n` (def-kun-topological-dimension-at-point).
Apply `Algebra.fibre_dimension_bounded_open_upstairs` at the coordinate prime of `x`
(lem-weil-pbc-fibre-dimension-bounded-open-upstairs) to obtain an open neighbourhood
where every local fibre dimension is at most `d`. Transport it back to `W` and hence
to `X`; it is contained in the locus since `d ≤ n`. The locus is the union of these
open neighbourhoods. An empty locus is the empty union and is also open. -/
theorem isOpen_localFibreDimension_le {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (n : ℕ) :
    IsOpen {x : X | topologicalKrullDimAt (f.asFiber x) ≤ (n : WithBot ℕ∞)} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hfinite : ∃ d : ℕ,
      topologicalKrullDimAt (f.asFiber x) = (d : WithBot ℕ∞) := by
    have hnonneg : 0 ≤ topologicalKrullDimAt (f.asFiber x) := by
      refine le_iInf₂ fun U hxU ↦ ?_
      apply Order.krullDim_nonneg_iff.mpr
      exact ⟨⟨closure {⟨f.asFiber x, hxU⟩}, isIrreducible_singleton.closure,
        isClosed_closure⟩⟩
    have hle : topologicalKrullDimAt (f.asFiber x) ≤ (n : WithBot ℕ∞) := hx
    generalize topologicalKrullDimAt (f.asFiber x) = e at hle hnonneg ⊢
    induction e using WithBot.recBotCoe with
    | bot => exact False.elim ((not_le_of_gt (by decide : (⊥ : WithBot ℕ∞) < 0)) hnonneg)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exact False.elim ((not_le_of_gt
          (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n))) hle)
      | coe e => exact ⟨e, rfl⟩
  obtain ⟨d, hd⟩ := hfinite
  obtain ⟨W, hxW, hW⟩ := exists_bounded_fibre_dimension_neighbourhood f x d hd
  refine mem_nhds_iff.mpr ⟨W, ?_, W.isOpen, hxW⟩
  intro y hy
  have hdn : (d : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
    exact hd ▸ hx
  exact (hW y hy).trans hdn

end AlgebraicGeometry
