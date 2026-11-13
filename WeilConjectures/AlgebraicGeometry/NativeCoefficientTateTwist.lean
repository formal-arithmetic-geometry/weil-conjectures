/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TateTwist.ProEtale

/-! # Tate lines over an arbitrary condensed coefficient ring
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (phi : Profinite.continuousMapRingObj ℤ_[ell] ⟶ Λ) [IsMonHom phi]

/-- The first Tate line is ordinary scalar extension of the integral Tate module. -/
def sfCondensedTateTwistOne :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  (Mod.extendScalars (coefficientMap phi X)).obj (tateModule X ell)

/-- Nonnegative tensor powers of the actual first Tate line. -/
def sfCondensedTateTwistNat :
    ℕ → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  | 0 => 𝟙_ _
  | n + 1 => sfCondensedTateTwistNat n ⊗ sfCondensedTateTwistOne X ell Λ phi

/-- Signed powers: a negative power is the internal dual of the opposite positive power. -/
def sfCondensedTateTwist :
    ℤ → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  | (n : ℕ) => sfCondensedTateTwistNat X ell Λ phi n
  | .negSucc n => (ihom (sfCondensedTateTwistNat X ell Λ phi (n + 1))).obj (𝟙_ _)

/-- The same native coefficient line placed in degree zero of the ordinary derived category. -/
def sfCondensedTateTwistDerived (d : ℤ) :=
  (DerivedCategory.singleFunctor _ 0).obj (sfCondensedTateTwist X ell Λ phi d)

/-- For condensed Qbar coefficients this is the existing upstream Tate line, literally. -/
theorem sfCondensedTateTwist_qbar (X : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (d : ℤ) :
    sfCondensedTateTwist X ell (Profinite.padicAlgClRingObj ell)
      (Profinite.padicIntRingObjToPadicAlgCl ell) d = tateTwist X ell d := by
  have hn (n : ℕ) : sfCondensedTateTwistNat X ell (Profinite.padicAlgClRingObj ell)
      (Profinite.padicIntRingObjToPadicAlgCl ell) n = tateTwistNat X ell n := by
    induction n with
    | zero => rfl
    | succ n hn =>
      dsimp only [sfCondensedTateTwistNat, tateTwistNat]
      rw [hn]
      rfl
  cases d with
  | ofNat n => exact hn n
  | negSucc n =>
    dsimp only [sfCondensedTateTwist, tateTwist]
    rw [hn]

end AlgebraicGeometry.ProEtale
