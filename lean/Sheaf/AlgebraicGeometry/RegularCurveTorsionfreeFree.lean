/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.TorsionSubsheafQuotient
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.KrullDimension

/-!
# Torsion-free coherent modules on regular curves

Source: Stacks Project, Divisors, Tag 0CC4; constant rank on connected schemes
(blueprint: lem-sc-regular-curve-torsionfree-free).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- On an integral regular scheme of dimension at most one, a coherent module has zero
 torsion subsheaf exactly when it is finite locally free. In that case its rank is constant
 and is the dimension of its generic stalk over the function field. The torsion subsheaf
 is zero exactly when every stalk has no nonzero torsion element, since its stalks are the
 torsion submodules (`lem-sc-torsion-subsheaf-quotient`); torsion-free is written stalkwise,
 in the form of that lemma's quotient clause.
Source: Stacks Project, Divisors, Tag 0CC4
(blueprint: lem-sc-regular-curve-torsionfree-free).

Proof:
1. The affine regularity hypothesis (`def-weil-regular-scheme`) makes every stalk a
Noetherian regular local domain. The dimension bound makes it a field or a DVR, using
`lem-sc-regular-dim1-dvr`. Coherence (`pqf-def-coherent`) makes the module stalk finite.
2. Zero torsion subsheaf implies torsion-free stalks by `lem-sc-torsion-subsheaf-quotient`.
Over a field the finite stalk is free; over a DVR use `lem-sc-dvr-fg-torsionfree-free`.
Then `lem-sc-coherent-free-stalks-locally-free` gives finite local freeness.
3. Conversely free stalks over the domain stalks of `def-pc-integral-scheme` have no
nonzero torsion. By `lem-sc-torsion-subsheaf-quotient` the torsion subsheaf has zero stalks,
and hence is zero.
4. Finite local freeness gives locally constant rank. Integrality makes the space
connected, so this rank is constant. At the generic point its scalar ring is the
function field (`def-sc-function-field`), and the common rank is its vector-space dimension.
-/
theorem regular_curve_torsionfree_iff_finiteLocallyFree (X : Scheme.{u}) [IsIntegral X]
    (hregular : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ IsRegularRing Γ(X, U))
    (hdim : topologicalKrullDim X ≤ 1) (F : X.Modules)
    (hcoherent : RingedSpace.IsCoherent X.toRingedSpace F) :
    ((∀ (x : X) (s : F.presheaf.stalk x) (a : X.presheaf.stalk x),
        a ≠ 0 → a • s = 0 → s = 0) ↔ F.IsFiniteLocallyFree) ∧
    (F.IsFiniteLocallyFree →
      F.IsFiniteLocallyFreeOfRank
        (Module.finrank X.functionField (F.presheaf.stalk (genericPoint X)))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
