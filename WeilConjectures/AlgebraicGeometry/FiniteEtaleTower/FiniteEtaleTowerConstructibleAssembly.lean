/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTower.FiniteEtaleTowerConstructibleTermDescent

/-! # Assembly of finite etale tower descent data

This isolates the finite differential descent, eventual zero-composite equations, and
finite-Tor/constructibility verification after the terms have been placed at one stage.
(blueprint: lem-sf-finite-etale-tower-constructible-assembly)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.FiniteEtaleTower

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Assemble termwise finite-stage data into a descended bounded constructible finite-Tor
object.  The proof lifts each differential by the constructible Hom-colimit comparison,
refines the finitely many lifts until every consecutive composite is zero, and forms the
resulting finite-stage complex.  Constructible Serre closure supplies its cohomology models;
the faithful-flat pullback criterion preserves the finite Tor interval, and the induced
quasi-isomorphism identifies its pullback with the selected representative model.  Source:
Stacks Project
Tags 03TT and 09YU (3), finite complex descent.
(blueprint: lem-sf-finite-etale-tower-constructible-assembly) -/
theorem finiteEtaleTower_constructible_assembly
    [Finite k] [Algebra.IsSeparable k L]
    [LocallyOfFiniteType y] [QuasiCompact y] [IsSeparated y]
    (K : towerComplex A (limitScheme (L := L) y))
    (d : TermStageData y A K) :
    ∃ (P_i : C A (stage y d.i.val)),
      Nonempty ((pull A (projection y d.i.val)).obj P_i.obj ≅
        (_root_.DerivedCategory.Q).obj d.model) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteEtaleTower
