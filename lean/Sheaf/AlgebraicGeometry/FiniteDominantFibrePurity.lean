/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Irreducible
public import WeilConjectures.AlgebraicGeometry.NormalScheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.Sober
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents

/-!
# Purity of fibres under a finite dominant integral cover

Source: Stacks Project, Morphisms, Tag 02FZ (lemma-openness-bounded-dimension-fibres),
Algebra Tags 00OK and 00OY, and Varieties Tag 0A21
(blueprint: lem-trf-finite-dominant-fibre-purity).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite dominant map between integral schemes of finite type over an integral Noetherian
base transfers pure dimension of every nonempty fibre from its target to its source.

Source: Stacks Project, Morphisms, Tag 02FZ (lemma-openness-bounded-dimension-fibres),
Algebra Tags 00OK and 00OY, and Varieties Tag 0A21
(blueprint: lem-trf-finite-dominant-fibre-purity).

Proof:
1. Finiteness makes `r` closed by `lem-weil-pbc-finite-closed-map-finite-fibres`.
   Dominance (`def-sbc-normal-dominant-galois`) then makes it surjective. For every `s`,
   its base change `D_s → C_s` is finite and surjective by
   `lem-weil-pbc-finite-morphism-permanence` and `lem-weil-pbc-surjective-base-change`.
   Both fibres are finite type over the residue field and Noetherian by
   `lem-sfb-finite-type-composition-base-change` and `lem-weil-pbc-finite-type-over-noetherian`.
   They are nonempty at exactly the same base points.
2. Let `ξ_D` and `ξ_C` be the generic points of the integral total spaces
   (`def-pc-integral-scheme`, `lem-sc-scheme-sober`, `def-sc-generic-point`). Continuity and
   surjectivity give `r(ξ_D) = ξ_C`. Their common base image `t` need not be generic in `S`.
   By `def-pc-scheme-fibre`, `D_t` is homeomorphic to the subspace `f⁻¹(t)` containing `ξ_D`.
   Every nonempty relative open comes from a nonempty open in `D`, hence contains `ξ_D`.
   Thus `D_t` is irreducible. The same argument proves `C_t` irreducible and nonempty.
3. The unique component of `C_t` has dimension `n` by the hypothesis. The finite surjection
   `D_t → C_t` and `lem-sc-finite-surjective-dimension` give `dim D_t = n`.
   By `lem-sc-dimension-locally-algebraic`, local dimension at the point of `D_t`
   corresponding to `ξ_D` is `n`.
4. For `n > 0`, `lem-weil-pbc-local-fibre-dimension-open` makes the locus in `D` of local
   fibre dimension at most `n - 1` open. Step 3 excludes `ξ_D`, so this open is empty:
   every nonempty open contains `ξ_D` by `def-sc-generic-point`. All local fibre dimensions
   are therefore at least `n`. For `n = 0`, this follows directly from nonnegativity of
   local dimension at a point (`def-kun-topological-dimension-at-point`).
5. On any nonempty `C_s`, `lem-sbc-equidimensional-open-local-dimension` gives constant local
   dimension `n`. By `lem-weil-pbc-dimension-supremum-local-dimensions`, `dim C_s = n`.
   The finite surjection gives `dim D_s = n` by `lem-sc-finite-surjective-dimension`.
   The whole fibre is an open neighbourhood of each point, so local dimension is at most
   `n`, by `def-kun-topological-dimension-at-point`.
6. Steps 4 and 5 give constant local dimension `n` on the Noetherian scheme `D_s`.
   Apply `lem-sbc-constant-local-dimension-components` to its whole open subset: all its
   components have dimension `n`. Empty fibres impose no condition. -/
theorem finite_dominant_fibre_purity
    (S C D : Scheme.{u})
    (f : D ⟶ S) (h : C ⟶ S) (r : D ⟶ C)
    [IsIntegral S] [IsNoetherian S]
    [IsIntegral C] [IsIntegral D]
    [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType h] [QuasiCompact h]
    [IsFinite r] [IsDominant r]
    (hr : r ≫ h = f)
    (n : ℕ)
    (hn : ∀ s : S, Nonempty (h.fiber s) →
      ∀ Z ∈ irreducibleComponents (h.fiber s), topologicalKrullDim Z = (n : WithBot ℕ∞)) :
    ∀ s : S, Nonempty (f.fiber s) →
      ∀ Z ∈ irreducibleComponents (f.fiber s), topologicalKrullDim Z = (n : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
