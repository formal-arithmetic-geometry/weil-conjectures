/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Defs
public import WeilConjectures.WeilSheaf.TateTwist

/-!
# Rank-one Thom map on sheaf objects

The integral divisor class of the zero section is compatible with reduction modulo the
uniformizer.  The finite-fibre calculation identifies its reduction with compactly supported
cohomology of the affine line, and derived completeness then makes the natural Thom map
`P(-1)[-2] ⟶ Rπ_! π^* P` invertible on the complexes arising from Weil sheaves.  The
remaining dévissage from sheaf objects to arbitrary bounded complexes is recorded separately.

Source: latest blueprint `thm-pur-rank-one-thom`, Steps 1--4.
(blueprint: lem-pur-rank-one-native-sheaf-thom)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- The integral reduction and finite-fibre route supplies the Thom transformation
`σ : P(-1)[-2] ⟶ Rπ_! π^* P`, invertible on objects coming from Weil sheaves.  It points in the
direction of the class: no inverse, and no dévissage of a general complex, is used here.

Proof in words.  Construct the compatible finite Kummer classes of the zero section and pass to
their inverse limit to obtain the integral class; compact-support direct image gives
`τ_V : Λ_X → Rπ_!Λ_Y(1)[2]`, and untwisting by the perfect line `Λ_X(-1)[-2]` (projection
formulas for `j_!` and `Rr_*`) gives `Λ_X(-1)[-2] → Rπ_!Λ_Y`.  Tensoring with `P` and the
projection map `P ⊗ Rπ_!Λ_Y → Rπ_!(π^*P)` give `σ_P`, natural and compatible with shifts.
At a geometric point of `X`, the finite-fibre calculation identifies the first reduction of
`τ_V` with `A₁ → RΓ_c(𝔸¹,A₁(1)[2])`, sending `1` to the supported origin class, hence with an
isomorphism.  Derived completeness of both endpoints and of the cone, followed by derived
Nakayama, makes the integral `τ_V` invertible; scalar comparison transports this to `E` and
`Q̄_ℓ`.  The projection formula then makes `σ_P` invertible for every Weil sheaf `P`.
(blueprint: lem-pur-rank-one-native-sheaf-thom)
-/
theorem WeilComplex.exists_rankOneThom_on_toComplex
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
      NatTrans.CommShift σ ℤ ∧ ∀ P : WeilSheaf k₀ l X,
        IsIso (σ.app ((WeilSheaf.toComplex (k₀ := k₀) (l := l) (X := X)).obj P)) := by
  sorry

end AlgebraicGeometry
