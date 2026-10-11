/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Finite flat pushforwards are locally free of locally constant rank

Source: Stacks Project, Morphisms of Schemes, Tags 02KB and 04MH
(blueprint: lem-sc-finite-pushforward-locally-free).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite, flat, locally finitely presented morphism `f : X ⟶ Y` has a structure-sheaf
pushforward `f_* 𝒪_X` which is a finite locally free `𝒪_Y`-module
(`SheafOfModules.IsFiniteLocallyFree`, Stacks 01C6), with locally constant rank: there is a
locally constant `d : Y → ℕ` such that on every open `U` on which `d` is constant equal to `n`
the restriction `(f_* 𝒪_X)|_U` is finite locally free of rank `n`. The fibres of `d` are the
disjoint open and closed pieces of constant rank.

Source: Stacks Project, Morphisms of Schemes, Tags 02KB and 04MH.
(blueprint: lem-sc-finite-pushforward-locally-free)

Proof: First, `def-pc-finite-locally-free` identifies the three hypotheses with finite local
freeness of the morphism. Apply `lem-weil-pbc-finite-locally-free-degree-locally-constant` to
partition the base into open and closed pieces of constant degree. On the degree-`n` piece,
`lem-pc-flf-properties` identifies the pushforward of the structure sheaf with a locally free
module of rank `n`. Restriction of direct image to that open piece is the direct image of the
restricted morphism: both have sections `O_X(f⁻¹(V))` on an open `V` in the piece. Combining
these local trivializations gives the required cover, and putting `d = n` on each piece gives
a locally constant rank function. The degree-zero piece has empty inverse image and zero
pushforward, so the same argument includes rank zero. -/
theorem isFiniteLocallyFree_pushforward_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
        ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) ∧
      ∃ d : Y → ℕ, IsLocallyConstant d ∧ ∀ (U : Y.Opens) (n : ℕ), (∀ y ∈ U, d y = n) →
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).over U) n := by
  sorry

end AlgebraicGeometry.Scheme.Modules
