/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfLocalizationData

import WeilConjectures.AlgebraicGeometry.FiniteKernelConstructibleLocalization
import WeilConjectures.AlgebraicGeometry.FiniteExceptionalSiteNormalization
import WeilConjectures.AlgebraicGeometry.SupportedTorReductionPropagation
import WeilConjectures.AlgebraicGeometry.ImmersionResidueTorIntervals
import WeilConjectures.AlgebraicGeometry.ProEtaleOpenResidueTorBound
import WeilConjectures.AlgebraicGeometry.OpenGeneralFieldUniformBound

/-! # Supported localization at one positive finite level

Source: current blueprint, supported localization, finite parts of (1)--(4)
and Finite Tor amplitude (1')--(4').
(blueprint: lem-sf-positive-finite-localization-construction). -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Construct one finite localization record, without integral operations or reductions.

Source: current blueprint, prop-sf-localization-all-stages.proof.md, finite parts of
(1)--(4), Finite Tor amplitude (1') and (2').
(blueprint: lem-sf-positive-finite-localization-construction).

Proof: use finiteKernelConstructibleLocalization at exponent n+1. Restrict its five
functors to the full intrinsic constructible subcategories, using its preservation
clauses. Fully faithful inclusions restrict the three adjunctions with their actual
units and counits; the ordinary pullback and direct-image comparisons give the four
recorded functor isomorphisms and both unit equations. Transport its supported triangle
through those comparisons. Shifted closed-to-open Hom vanishing makes the connecting
arrow unique and natural. Closed full faithfulness makes the exceptional unit invertible;
Hom orthogonality and the exceptional adjunction show that exceptional after open image
is zero. For the specified exceptional comparison, use torsion site comparison over k
on bounded-below constructible complexes and identify the two right adjoints to closed
image by their Hom bijections. Normalize by the counit. This is the argument of
finiteExceptionalSiteNormalization; its finite-field hypothesis is not used as an input.
For the quantitative fields, exact monoidal pullback preserves the residue tensor and
its cohomological interval. Closed image has zero restriction to U, so its residue
interval is detected on Z. Transport these assertions between fixed-module coordinates
and intrinsic coordinates (including the coefficient universe). The general-field bound
for Rj_* on etale sheaves is 2d+c; if U is empty all images are zero and d=0. The open
residue projection formula and residue criterion give the open Tor interval. Inversely
rotate the supported triangle, tensor with the residue module, and use the homology
exact sequence to bound i_*Ri!K in [a,b+2d+c+1]. Closed pullback and its invertible
counit give this same bound for Ri!K. Choosing intervals gives the five finite-Tor
preservation clauses. This argument includes n=0, zero objects, and empty Z or U. -/
theorem sfPositiveFiniteLocalizationConstruction
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (t : X ⟶ Spec (.of k))
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    {Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ) (n : ℕ) :
    Nonempty (SfFiniteLocalization l E n k i j) := by sorry

end WeilConjectures
