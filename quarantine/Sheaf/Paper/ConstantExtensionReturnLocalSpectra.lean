/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.Paper.ConstantExtensionReturnData

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

/-- Common-stage local spectra and residue degrees for a functor satisfying the
specified sheet-return formula. This precedes all purity and filtration claims.
Source: Deligne, Weil II (1.1.8)--(1.1.10), pp. 151--152.
(blueprint: lem-zl-sheet-return-local-spectra).

Proof: a basis for the closed residue field over k_m, followed by a basis for
k_m over k_0, gives degree mr over k_0 and cardinality (q^m)^r=q^(mr).
Choose compatible geometric points on the distinguished sheet. Descend each
object, Weil structure, inverse and carrier comparison to a common finite
coefficient field; the sheet specification becomes its finite return formula.
Apply the rational operator identity there, and its scalar compatibility after
any further common extension. Taking degree-zero fibre cohomology and extending
to the algebraic closure gives an intertwining isomorphism. For arbitrary
residue embeddings compose with the local Frobenius conjugacy comparisons on
the two sides. This proves the displayed local conjugacy for every pair of
presentations. An intertwining linear isomorphism carries each nonzero
eigenvector to a nonzero eigenvector of the same eigenvalue; its inverse gives
the reverse implication. Every finite presentation can be compared after a
common coefficient extension, so the existential common-stage spectra agree.
Zero stalks contribute no eigenvalues. -/
theorem sheetReturnLocalSpectra
    (R : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (hR : ConstantExtensionSheetSpec D m hm X₀ l hl Ω R)
    (hops : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E],
      SheetReturnRationalOperators D m hm X₀ l hl E ∧
        SheetReturnScalarCompatibility D m hm X₀ l hl E) :
    (∀ (N : sfCommonStageWeilSheaf D l hl
        (constantExtensionOriginalModel D m hm X₀) Ω)
      (z : {z : (constantExtensionModel D m hm X₀).left //
        z ∈ closedPoints (constantExtensionModel D m hm X₀).left}) (α : Ω),
      SfPunctualEigenvalue D l hl Ω (constantExtensionOriginalModel D m hm X₀) N z α ↔
        SfPunctualEigenvalue (constantExtensionDatum D m hm) l hl Ω
          (constantExtensionModel D m hm X₀) (R.obj N) z α) ∧
    (∀ (z : {z : (constantExtensionModel D m hm X₀).left //
        z ∈ closedPoints (constantExtensionModel D m hm X₀).left}),
      localClosedPointDegree D (constantExtensionOriginalModel D m hm X₀) z =
        m * localClosedPointDegree (constantExtensionDatum D m hm)
          (constantExtensionModel D m hm X₀) z ∧
      Nat.card ((constantExtensionModel D m hm X₀).left.residueField z.val) =
        D.q ^ (m * localClosedPointDegree (constantExtensionDatum D m hm)
          (constantExtensionModel D m hm X₀) z)) ∧
    (∀ (N : sfCommonStageWeilSheaf D l hl
        (constantExtensionOriginalModel D m hm X₀) Ω)
      (z : {z : (constantExtensionModel D m hm X₀).left //
        z ∈ closedPoints (constantExtensionModel D m hm X₀).left}),
      ConstantExtensionLocalConjugacy D m hm X₀ l hl Ω
        (constantExtensionOriginalModel D m hm X₀) N (R.obj N) z z 1) := by sorry

end WeilConjectures
