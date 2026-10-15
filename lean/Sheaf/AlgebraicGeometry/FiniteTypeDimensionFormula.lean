/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.SetTheory.Cardinal.ENat
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.ZetaSeries
import Sheaf.RingTheory.DimensionAtPointLocalRingTrdeg

/-!
# Dimension formula for finite type schemes over a field

Source: Stacks Project, Morphisms, Lemma 29.29.1 (Tag 02FX), specialized to a field base;
blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-dimension-formula`
(blueprint: lem-kun-dimension-formula).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, Morphisms, Lemma 29.29.1 (Tag 02FX), over `Spec K`;
blueprint node `lem-kun-dimension-formula` (blueprint: lem-kun-dimension-formula).
For a finite type `K`-scheme, the local topological dimension at `x` equals the dimension
of its stalk plus the transcendence degree of its residue field. The residue-field algebra
is the canonical one induced by the structure morphism. `Cardinal.toENat` preserves each
finite cardinal and sends infinite cardinals to infinity, embedding the transcendence degree
in the same extended dimension type as the other terms.

Proof:
1. Write `f = X ↘ Spec K`. Choose an affine open neighbourhood `U` of `x` and put
   `R = Γ(X, U)`. By `lem-weil-pbc-lft-affine-pairs`, `R` is a finite type `K`-algebra.
   By `lem-weil-pbc-affine-open-spec-points`, `x` corresponds to a prime `p` of `R`.
2. By `lem-weil-pbc-dimension-at-point-open-subspace`, replacing `X` by `U` leaves its
   dimension at `x` unchanged. The affine homeomorphism identifies this with the dimension
   of `Spec R` at `p`, since it identifies open neighbourhoods and irreducible closed chains.
3. Apply `lem-weil-pbc-dimension-at-point-local-ring-trdeg` to `R` and `p`, obtaining
   `dim_p Spec R = dim R_p + trdeg_K κ(p)`, with finite terms. This applies to reducible
   and nonreduced algebras as well.
4. By `lem-weil-pbc-affine-open-stalk-localization`, `R_p` is isomorphic to the stalk
   at `x` via `r/s ↦ r_x / s_x`. Constants map to their germs, so this is a `K`-linear
   ring isomorphism. It identifies maximal ideals and hence the residue fields over `K`.
   Prime chains and algebraically independent subsets correspond under these isomorphisms,
   preserving ring dimension and transcendence degree. Substitution gives the formula. -/
theorem topologicalKrullDimAt_eq_stalk_dimension_add_residue_trdeg
    {K : Type u} [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] (x : X) :
    topologicalKrullDimAt x = ringKrullDim (X.presheaf.stalk x) +
      (Cardinal.toENat (@Algebra.trdeg K (X.residueField x) _ _
        ((X ↘ Spec (.of K)).residueFieldAlgebraMap x).toAlgebra) : WithBot ℕ∞) := sorry

end AlgebraicGeometry
