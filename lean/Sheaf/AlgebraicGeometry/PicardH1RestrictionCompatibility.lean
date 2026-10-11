/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.ZariskiUnitsRestriction

/-!
# Picard restriction and first cohomology of units

Source: Stacks Project, Tag 09NY, final sentence of the proof, with Tags 02UV and 09NU
(blueprint: lem-sc-picard-h1-restriction-compatibility).
-/

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The Hilbert-90 identification sends restriction of an invertible module to restriction
of its cohomology class. The existential witness asserts invertibility of the tensor pullback
and makes its Picard class typeable without imposing an additional hypothesis.

Source: Stacks Project, Tag 09NY, final sentence, with Tags 02UV and 09NU
(blueprint: lem-sc-picard-h1-restriction-compatibility).

Proof:
1. By thm-sc-hilbert-90, the class of `L` corresponds to the Zariski units torsor
   `Isom(O_X,L)` of its local generators.
2. A local generator `s` pulls back to `1 ⊗ s`. The identity
   `1 ⊗ us = i♯(u)(1 ⊗ s)` identifies the pushout along `O_Xˣ → i_* O_Zˣ` with
   `i_* Isom(O_Z,i*L)`. Clause (1) of lem-sc-torsor-h1-functoriality identifies their
   cohomology classes (using def-pc-module-pullback).
3. The canonical closed-immersion comparison of
   lem-sc-cohomology-closed-immersion-pushforward and clause (2) of
   lem-sc-torsor-h1-functoriality send this class to `Isom(O_Z,i*L)`.
   Applying thm-sc-hilbert-90 on `Z` gives the asserted equality. -/
theorem picard_h1_restriction_compatibility {Z X : Scheme.{v}} (i : Z ⟶ X)
    [IsClosedImmersion i] (L : X.Modules) [Modules.IsInvertible L] :
    ∃ h : Modules.IsInvertible ((Modules.tensorPullback i).obj L),
      unitsPushforwardCohomologyComparison i 1
        (Sheaf.H.map (unitsSheafToPushforward i) 1
          (Pic.toH1Units X (Pic.ofIsInvertible L))) =
        Pic.toH1Units Z (@Pic.ofIsInvertible Z ((Modules.tensorPullback i).obj L) h) := by
  sorry

end AlgebraicGeometry.Scheme
