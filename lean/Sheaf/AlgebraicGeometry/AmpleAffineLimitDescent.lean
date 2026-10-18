/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.ValuationLimitQcohSectionDescent

/-!
# Descent of ampleness along affine inverse limits

Source: Stacks Project, Limits, Tag 09MT, lemma-limit-ample, in Situation 01YX
(situation-descent) (blueprint: lem-trf-ample-affine-limit-descent).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- Ampleness of the pullback of an invertible module along an affine inverse limit
descends to one stage of the inverse system.
(blueprint: lem-trf-ample-affine-limit-descent)

Source: Stacks Project, Limits, Tag 09MT, lemma-limit-ample, in Situation 01YX.

Proof:
1. By `def-weil-pbc-ample-invertible-module`, each point of the limit lies in an
   affine nonvanishing locus of a section of a positive tensor power. Quasi-compactness
   gives finitely many such sections covering the limit, possibly of different powers.
2. Invertible modules and their powers are quasi-coherent. Apply
   `lem-sc-valuation-limit-qcoh-section-descent` to each corresponding power of `L₀`
   on the tail above `i₀`, then choose a common upper bound for their descent stages.
3. Pullback preserves nonvanishing loci. By `lem-weil-pbc-limit-affine-transition`,
   each of these opens on the limit is the affine-transition limit of the corresponding
   stage opens. By `lem-weil-pbc-limit-affine-stage`, those stage opens are eventually
   affine. A common upper bound makes all of them affine at once.
4. Their finite union is a quasi-compact open whose inverse image is the whole limit.
   Clause (2) of `pqf-lem-limit-qc-open-descends` makes its pullback equal the whole
   stage after increasing the index once more. Affineness persists because the
   transitions are affine.
5. The pulled-back module is invertible and its affine nonvanishing opens cover that
   quasi-compact stage, so it is ample by `def-weil-pbc-ample-invertible-module`.
-/
theorem exists_stage_isAmple_of_limit_isAmple
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D) (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj (op i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (op i))]
    (haff : ∀ {i j : I} (h : i ≤ j), IsAffineHom (D.map (homOfLE h).op))
    (i₀ : I) (L₀ : (D.obj (op i₀)).Modules) [L₀.IsInvertible]
    (hL : ∃ h : ((tensorPullback (c.π.app (op i₀))).obj L₀).IsInvertible,
      @IsAmple c.pt ((tensorPullback (c.π.app (op i₀))).obj L₀) h)
    : ∃ (j : I) (hij : i₀ ≤ j),
      ∃ h : ((tensorPullback (D.map (homOfLE hij).op)).obj L₀).IsInvertible,
        @IsAmple (D.obj (op j)) ((tensorPullback (D.map (homOfLE hij).op)).obj L₀) h := by
  sorry

end AlgebraicGeometry
