/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.CategoryTheory.HypercohomologyLeftEdge

import Sheaf.CategoryTheory.CartanEilenbergExists
import Sheaf.Paper.CartanEilenbergLeftExactCohomology
import Sheaf.CategoryTheory.TruncationHypercohomology

/-! # The cocycle equation for the hypercohomology left edge

Source: Stacks Project, derived.tex, Tag 015J, the second spectral sequence.
(blueprint: lem-pc-hypercohomology-edge-cocycle).
-/

@[expose] public section

universe uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The derived unit and the left edge send a cocycle to its quotient after `G`.
Source: Stacks Project, Tag 015J; the representative calculation in step 3 of
lem-pc-grothendieck-cocycle-comparison
(blueprint: lem-pc-hypercohomology-edge-cocycle).

Proof:
Extend K by zero and choose a Cartan--Eilenberg resolution. The injective horizontal
cycles, boundaries and cohomology give split short exact sequences in each
resolution degree, so G commutes with horizontal cohomology there. The second
filtration takes the resolution-degree-zero component of a total cocycle. The
unit sends c to the augmentation of G of the cycle inclusion, by the inclusion
hypothesis. Naturality of the homology quotient for the augmentation identifies
that component with G of the quotient Z^n(K) -> H^n(K), followed by the horizontal
cohomology augmentation. That augmentation lies in the kernel of the resolution
differential. There are no incoming boundaries in resolution degree zero.
Its kernel identifies with G(H^n(K)) by left exactness; the stable-page inclusion
preserves the representative and the transpose sign is (-1)^(n*0)=1.
The truncation spectral object is the canonical realization of this filtration;
its target identification is the truncation/shift/degree-zero composite in
hypercohomologyLeftEdgeTargetIso. Cancel the extension homology isomorphisms.
This gives the asserted equality for every supplied c; monicity of iCycles
makes the supplied c the unique lift of G of the inclusion. No acyclicity
of K's terms is required: the derived unit, rather than an abutment isomorphism,
is used on the source. This includes n=0, where the incoming differential is zero.
-/
theorem cochainHypercohomologyLeftEdge_cocycle
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    (K : CochainComplex B ℕ) (n : ℕ)
    (c : G.obj (K.cycles n) ⟶
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).cycles n)
    (hc : c ≫ ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles n =
      G.map (K.iCycles n)) :
    c ≫ ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ n ≫
        G.cochainHypercohomologyLeftEdge K n = G.map (K.homologyπ n) := by
  sorry

end CategoryTheory.Functor
