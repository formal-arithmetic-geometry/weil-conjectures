/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Defs
public import WeilConjectures.WeilSheaf.TateTwist

/-! # Off-degree vanishing for rank-one Thom

The affine-line fibre calculation for sheaf objects, away from the degree of the generator, is
isolated here.
Source: latest blueprint `thm-pur-rank-one-thom`, Step 2 ("all other supported cohomology
vanishes").
(blueprint: lem-pur-rank-one-native-finite-fibre)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- Both `Rπ_! π^* P` and `P(-1)[-2]` have zero homology sheaves away from degree two.

Proof in words.  The target: the Tate twist of the Weil sheaf `P` is again a Weil sheaf, so
`P(-1)[-2]` has homology only in degree two.  The source: by the projection formula
`Rπ_! π^* P ≅ P ⊗ Rπ_! Λ_Y`.  At a geometric point the stalk of `Rπ_! Λ_Y(1)[2]` is
`RΓ_c(𝔸¹, Λ(1)[2])`; the finite affine-line calculation gives `H^i_c(𝔸¹, A_n(1)) = 0` for
`i ≠ 2`, and the reduction, derived completeness and derived Nakayama route of the parent
theorem, followed by scalar comparison, gives `Rπ_! Λ_Y ≅ Λ_X(-1)[-2]`.  Hence
`Rπ_! π^* P ≅ P(-1)[-2]` has homology only in degree two.  The statement does not involve the
Thom transformation.
(blueprint: lem-pur-rank-one-native-finite-fibre)
-/
theorem WeilComplex.rankOneThom_offDegree_zero
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (π : Y ⟶ X) (s : Y ⟶ affineLine k₀)
    [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (P : WeilSheaf k₀ l X) {r : ℤ} (hr : r ≠ 2) :
    IsZero ((WeilComplex.homologySheaf r).obj
      ((WeilComplex.upperStar π ⋙ WeilComplex.derivedLowerShriek k₀ l π).obj
        ((WeilSheaf.toComplex (k₀ := k₀) (l := l) (X := X)).obj P))) ∧
      IsZero ((WeilComplex.homologySheaf r).obj
        ((WeilComplex.tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)).obj
          ((WeilSheaf.toComplex (k₀ := k₀) (l := l) (X := X)).obj P))) := by
  sorry

end AlgebraicGeometry
