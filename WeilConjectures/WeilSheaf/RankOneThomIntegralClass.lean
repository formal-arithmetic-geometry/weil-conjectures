/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Defs
public import WeilConjectures.WeilSheaf.TateTwist

/-! # Integral rank-one Thom transformation

The integral divisor-class construction, its untwisting, and its degree-two homology on sheaf
objects are isolated here.  The transformation points in the direction of the class,
`K(-1)[-2] ⟶ Rπ_! π^* K`.
Source: latest blueprint `thm-pur-rank-one-thom`, Steps 1--2.
(blueprint: lem-pur-rank-one-native-integral-class)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- Construct the shift-compatible Thom transformation `σ : K(-1)[-2] ⟶ Rπ_! π^* K` supplied by
the integral zero-section class, invertible on degree-two homology of every sheaf object.

Proof in words.  On every finite quotient `A_n` of the integral coefficient ring, take the Kummer
class of the zero divisor and its compact-support image `τ_{V,A_n} : A_n → Rπ_! A_n(1)[2]`.  The
coherent transition maps assemble these into the integral class `τ_{V,R}`, and derived scalar
extension gives its rational and algebraically closed coefficient versions `τ_V`.  Untwisting by
the perfect line `Λ_X(-1)[-2]` (projection formulas for `j_!` and `Rr_*`) gives
`Λ_X(-1)[-2] → Rπ_! Λ_Y`; tensoring with `K` and composing with the projection map
`K ⊗ Rπ_! Λ_Y → Rπ_! π^* K` gives `σ_K`, natural in `K` and compatible with shifts.  For a
Weil sheaf `P`, the stalk of `H²(σ_P)` at a geometric point is `P_x` tensored with the map
`Λ → H²_c(𝔸¹, Λ(1))` sending `1` to the supported class of the origin; by the finite-fibre
calculation its first reduction is the normalized generator, and derived completeness, derived
Nakayama and scalar comparison make it an isomorphism.  Stalks are conservative, so
`H²(σ_P)` is an isomorphism.
(blueprint: lem-pur-rank-one-native-integral-class)
-/
theorem WeilComplex.exists_rankOneThom_integral_class
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (π : Y ⟶ X) (s : Y ⟶ affineLine k₀)
    [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ (σ : WeilComplex.tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ) ⟶
        WeilComplex.upperStar π ⋙ WeilComplex.derivedLowerShriek k₀ l π),
      NatTrans.CommShift σ ℤ ∧
      ∀ P : WeilSheaf k₀ l X,
        IsIso ((WeilComplex.homologySheaf (2 : ℤ)).map
          (σ.app ((WeilSheaf.toComplex (k₀ := k₀) (l := l) (X := X)).obj P))) := by
  sorry

end AlgebraicGeometry
