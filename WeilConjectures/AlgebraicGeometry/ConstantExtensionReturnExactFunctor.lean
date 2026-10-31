/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantExtensionReturnData

/-! # Sheet return and its local weight filtrations

Source: Deligne, Weil II (1.1.7)--(1.1.10), pp. 150--152, and (1.2.6), p. 154
(blueprint: lem-zl-constant-extension-return-local-operators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v a b c d
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The sheet-return functor is an equivalence, with its actual carrier and ordered
Weil-map formula. Source: Deligne, Weil II, paragraph after (1.1.10), p. 152.
(blueprint: lem-zl-sheet-return-exact-functor).

Proof: use the clopen sheet-coordinate equivalence to write a Weil object as its
m carriers and successive transition isomorphisms. Restrict the cyclic-return
construction to the constructible heart. Its first carrier is the distinguished
sheet pullback, and its ordered transition product is the specified m-fold Weil
iterate by induction with the normalized pullback compositors. On arrows it is
restriction to sheet zero. The inverse repeats the first carrier and takes all
intermediate transitions to be identities; the final transition is the given
return. The partial transition products give the unit, while the counit is the
identity. Coordinate normalization gives ConstantExtensionSheetSpec. These
constructions include m=1, the zero object and the empty scheme. -/
theorem sheetReturnExactFunctor :
    ∃ R : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ⥤
        sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀) Ω,
      ConstantExtensionSheetSpec D m hm X₀ l hl Ω R ∧ R.IsEquivalence := by sorry

end WeilConjectures
