/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated

/-! # Vanishing of maps from a perfect complex across a cohomology gap

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.13.5(1), Tag 09M4,
label `lemma-ext-from-perfect-into-bounded-QCoh`
(blueprint: lem-sc-perfect-ext-bounded-qcoh-vanishing).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- On a quasi-compact and quasi-separated scheme, a perfect complex admits a finite
cohomology gap such that every object with quasi-coherent cohomology vanishing in that gap
receives only the zero morphism from it.
Source: Stacks Project, Derived Categories of Schemes, Lemma 36.13.5(1), Tag 09M4
(blueprint: lem-sc-perfect-ext-bounded-qcoh-vanishing).

Proof, following the node's four steps:
1. By `lem-pc-perfect-rhom-tensor-comparison`, the dual of `K` is perfect, with finite
Tor-amplitude `[u,v]`, and its derived tensor product with `L` is the derived internal Hom.
By `lem-pur-rhom-global-sections`, maps from `K` to `L` are its global degree-zero cohomology.
2. By `lem-sc-perfect-hypercohomology-gap`, vanishing of `H^i(L)` on `[j-v,j-u]` implies
vanishing of degree `j` of the derived tensor product. For every `j` in `[-N,0]`, the gap
`[-v-N,-u]` suffices.
3. Apply `lem-pc-finite-support-hi` to the qcqs map from `X` to `Spec Z`. Its higher direct
images of quasi-coherent sheaves are quasi-coherent and vanish uniformly in high degrees.
Use `lem-pc-affine-vanishing` and `lem-pc-leray-degenerate-sections` to obtain a nonnegative
uniform cohomological bound `N` for quasi-coherent sheaves on `X`. The tensor product has
quasi-coherent cohomology. Its truncation triangle at `-N` gives an exact sequence of global
cohomology. By `lem-pc-unbounded-derived-functor-cohomological-bound`, global degree-zero
cohomology of the lower tail vanishes. If its cohomology vanishes in `[-N,0]`, the upper
truncation is concentrated in degrees at least one, and
`lem-weil-pbc-derived-functor-negative-vanishing` kills its global degree-zero cohomology.
Thus global degree-zero cohomology of the tensor product vanishes.
4. Set `a = -v-N` and `b = -u`. Since `u ≤ v` and `0 ≤ N`, we have `a ≤ b`; the preceding
steps identify the Hom group with zero whenever `L` has the indicated gap. -/
theorem exists_subsingleton_hom_of_isPerfect (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K : schemeDerivedCategory X) (hK : IsPerfect X K) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ L : schemeDerivedCategory X,
      schemeDerivedQCohProperty X L →
      (∀ i : ℤ, a ≤ i → i ≤ b →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj L)) →
      Subsingleton (K ⟶ L) := by
  sorry

end AlgebraicGeometry.Scheme
