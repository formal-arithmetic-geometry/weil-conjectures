/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedAffineFreePresheafLocalDual
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Local linear tests on an affine completed free representable
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Local linear functionals into the completed coefficient ring detect sections
of the sheafified free module on a pro-affine etale representable.

Source: the canonical
clopen-neighborhood localizations of Stacks 097C give the closed restrictions below. -/
theorem completedAffineFree_localDual_detect (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ) (hU : proAffineEtale U.unop.hom) :
    let R := Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)
    let P := (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((PresheafOfModules.free R.obj).obj (uliftYoneda.{u + 1}.obj U.unop))
    ∀ (V : X.ProEtᵒᵖ) (x : P.val.obj V),
      (∀ (W : X.ProEt) (f : W ⟶ V.unop)
        (φ : P.over W ⟶ SheafOfModules.unit (R.over W)),
        φ.val.app (op (Over.mk (𝟙 W))) (P.val.map f.op x) = 0) → x = 0 := by
  dsimp
  intro V x hx
  let R := Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)
  let F := (PresheafOfModules.free R.obj).obj
    (uliftYoneda.{u + 1}.obj U.unop)
  let P := (PresheafOfModules.sheafification (𝟙 R.obj)).obj F
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app F
  let ηp := (PresheafOfModules.toPresheaf R.obj).map η
  have hη : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) ηp := by
    change Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
      (CategoryTheory.toSheafify (Scheme.ProEt.topology X) F.presheaf)
    infer_instance
  apply P.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem (Scheme.ProEt.topology X) ηp x)
  intro W f hf
  change P.val.map f.op x = P.val.map f.op 0
  obtain ⟨y, hy⟩ := hf
  change (η.app (op W) y) = P.val.map f.op x at hy
  by_cases hy0 : η.app (op W) y = 0
  · rw [← hy, hy0]
    simp only [map_zero]
  · obtain ⟨φ, hφ⟩ := completedAffineFree_presheaf_localDual l X U hU W y hy0
    have hz := hx W f φ
    rw [← hy] at hz
    exact False.elim (hφ hz)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
