/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.Curve.Reductions
import WeilConjectures.ConstructibleSheaf.LocallyConstantReduction
import WeilConjectures.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions
import WeilConjectures.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer
import Mathlib.Algebra.Category.ModuleCat.Algebra

/-! # Eight assertions for constructible prime coefficients on reduced curves

Source: Stacks Project, 03SC, 03SD, 0A3Q, 03SG.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- All eight assertions for a constructible prime-field sheaf on a reduced curve.

Source: Stacks Project, 03SC, constructible prime-field case. -/
theorem primeCoefficientCurveAssertions {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsReduced C]
    {r : ℕ} [Fact r.Prime]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    [Scheme.IsConstructibleSheaf F] :
    IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f F := by
  classical
  let R := ULift.{u + 1} (ZMod r)
  have hF : r • 𝟙 F = 0 := by
    have hr : (r : R) = 0 := by simp [R]
    rw [← Nat.cast_smul_eq_nsmul R, hr, zero_smul]
  obtain ⟨n, U, _hdense, _hdisjoint, hirr, _hdim, hlc, hlocal⟩ :=
    exists_dense_assertions_iff_forall_lowerShriek R f r F hF
  apply hlocal.mpr
  intro a
  have : IrreducibleSpace (U a) := Subtype.irreducibleSpace (hirr a)
  have := hlc a
  let G := (Etale.upperStar (ModuleCat.{u + 1} R) (U a).ι).obj F
  obtain ⟨V, v, hvfinite, hvetale, _hconnected, _d, _hdegree, _hfibres,
    ⟨m, W, ι, hzero, hend, hquot⟩, ρ, hρ⟩ :=
    Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_reduction r G
  have := hvfinite
  have := hvetale
  exact filteredFiniteCoverLowerShriekTransfer f (U a).ι r G v m W ι hzero hend hquot
    ρ hρ (by
      intro Y T g _ _ b _
      exact reducedConstantLowerShriekAssertions g b r)

end AlgebraicGeometry.IsCurve
