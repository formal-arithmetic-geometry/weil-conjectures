/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Category

/-!
# The lisse locus of a Weil sheaf

A Weil sheaf on a reduced `k₀`-scheme of finite type is lisse on a dense open subscheme
(generic lissity, used in blueprint `thm-zl-relative-line-stratification`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Generic lissity.** A Weil sheaf on a reduced `k₀`-scheme of finite type is lisse on a dense
open subscheme (blueprint: `thm-zl-relative-line-stratification`, the lissity loci chosen over
the finite-field model). -/
theorem WeilSheaf.exists_dense_isLisse_upperStar {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IsReduced X] (F : WeilSheaf k₀ l X) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ ((WeilSheaf.upperStar U.ι).obj F).IsLisse := by
  sorry

end AlgebraicGeometry
