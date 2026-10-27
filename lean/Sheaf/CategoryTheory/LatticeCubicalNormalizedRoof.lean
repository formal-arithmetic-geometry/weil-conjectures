/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.CategoryTheory.LatticeCubicalMultiplicationData

/-! # Normalized internal cubical diagonal and evaluation

Source: direct-images paragraph (3), lattice expansion, steps 1--3
(blueprint: lem-sfb-lattice-cubical-normalized-roof).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace Profinite.DiscreteLattice.CubicalMultiplication

variable (R : CategoryTheory.CondensedBar.Ring.{u}) (r : ℕ)
    (J : CubicalEvaluation.DiscreteComparison R r)
    (C : CubicalEvaluation.CubicalModel R r)
    (K : KoszulModel R.toMon r) (B : DerivedCup.Algebra R.toMon r)

/-- Construct the diagonal, augmentation and signed evaluation on any recorded cubical model.
Source: the internalization and coordinate part of steps 1--3 of the cubical roof argument
(blueprint: lem-sfb-lattice-cubical-normalized-roof).

Proof: use the coproduct universal property of C in each degree. The augmentation sends
vertices to 1 and other degrees to zero. Extend the integral diagonal R-linearly using
its finite partition formula, reindexing chain degree a to cochain degree -a. The integral
chain-map and counit equations then hold as equalities of integer matrices of internal
maps. Translation commutes with the formula, so transport along J gives equivariant maps.
For evaluation define the degree-zero matrix entry on a Koszul summand A and a cube I
as zero unless A=I, and otherwise c_p times T^v after the right unitor. The signed Hom
calculation of the augmentation-evaluation theorem proves the chain-map equation; its
horizontal and vertical sign recurrences cancel the two differentials. Equivalently,
transport the recorded evaluation from its canonical cubical model using the unique
cell-preserving isomorphism to C, and restrict to an algebra in degree zero. The
coproduct and finite biproduct universal properties yield the displayed normalization
identities. Both counits and the double counit come from the integral diagonal theorem.
All matrices have finite columns. In rank zero only the vertex exists; zero coefficients
and characteristic two need no exceptions. -/
theorem exists_normalized_roof :
    ∃ F : Roof (koszul R r K B) (lattice R r J C) (algebra R r B),
      Normalized R r J C K B F := by sorry

end Profinite.DiscreteLattice.CubicalMultiplication
