/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Sheaf.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg

/-!
# Coordinate projections lower generic dimension

Source: blueprint, sec-smooth-purity, sk-prop-sf-cbc,
lem-fin-coordinate-generic-dimension (blueprint: lem-fin-coordinate-generic-dimension).

The generic fibre over `S` is the fibre at `genericPoint S`, equivalently base change to
its function field. A strict bound by the natural number `n` expresses dimension at most
`n - 1`, including `n = 0`: only the empty scheme has dimension strictly below zero.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Every coordinate projection of an open subscheme of a closed subscheme of affine
space lowers the dimension of the generic fibre by one. Empty fibres have dimension `⊥`.
Source: blueprint, sec-smooth-purity, sk-prop-sf-cbc,
lem-fin-coordinate-generic-dimension (blueprint: lem-fin-coordinate-generic-dimension).

Proof:
1. Scheme sobriety and integrality give generic points of `S` and its affine line.
   On a nonempty affine base chart `Spec R`, the integral function-field affine-fraction
   lemma identifies their generic residue fields with `K = Frac R` and `K(T)`.
   Clearing coefficient denominators identifies `Frac R[T]` with `K(T)`.
   The fibre-product universal property identifies the indicated fibre with the generic
   fibre of the same coordinate on `X_K`; no Noetherian hypothesis on `S` is used.
2. The composite of the open and closed immersions is an immersion. Base change preserves
   immersions, which are locally of finite type. Affine space is locally of finite type
   over the field, so composition and the affine-pairs criterion show every affine open
   `Spec C` of `X_K` has a finitely generated `K`-algebra as coordinate ring.
3. Finite affine tensor base change and the fibre-ring localization theorem identify its
   coordinate generic fibre with `Spec D`, where `D = C ⊗[K[T]] K(T) = W⁻¹C` and
   `W = {h(t) | h ≠ 0}`. The same generators make `D` finite type over `K(T)`.
   The open-fibre-product lemma gives an open cover of the whole fibre by these charts.
4. Localization prime and residue-field correspondence associates to each prime `Q` of
   `D` a prime `p` of `C` avoiding `W`, and identifies their residue fields `E`.
   Thus `K[T]` injects into `E`. The closed-irreducible dimension/transcendence-degree
   theorem gives `trdeg_K E = dim V(p) ≤ dim X_K ≤ n`; the middle inequality follows
   by taking closures of strict chains in the open chart.
5. The transcendence-degree tower formula and the transcendence basis `{T}` of `K(T)`
   give `trdeg_K E = trdeg_{K(T)} E + 1`. Hence the same dimension theorem over `K(T)`
   bounds `dim V(Q)` by `n - 1`. If `n = 0`, there can be no such prime.
6. Every finite chain of irreducible closed subsets of `Spec D` lies in its largest
   member `V(Q)`, so has length at most `n - 1`. For a chain in the whole fibre choose
   an affine fibre chart containing the generic point of its smallest member. Opens
   are stable under generalization, so all generic points lie in this chart; intersection
   preserves strictness since closures recover the original members. Taking the supremum
   of chain lengths gives the bound, with dimension `⊥` for an empty fibre. Nilpotents
   do not affect the prime ideals or these chains. -/
theorem coordinate_generic_fiber_dimension_lt
    (S : Scheme.{u}) [IsIntegral S] {m n : ℕ} {X Y : Scheme.{u}}
    (i : Y ⟶ AffineSpace (ULift.{u} (Fin m)) S) [IsClosedImmersion i]
    (j : X ⟶ Y) [IsOpenImmersion j]
    (hdim : topologicalKrullDim
      ((j ≫ i ≫ (AffineSpace (ULift.{u} (Fin m)) S ↘ S)).fiber (genericPoint S)) ≤
        (n : WithBot ℕ∞)) (r : Fin m) :
    topologicalKrullDim
      ((j ≫ i ≫ AffineSpace.reindex
        (fun _ : ULift.{u} (Fin 1) ↦ (ULift.up r : ULift.{u} (Fin m))) S).fiber
          (genericPoint (AffineSpace (ULift.{u} (Fin 1)) S))) < (n : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
