/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero

/-!
# Ordinary condensed middle image and its canonical Weil structure

Source: latest blueprint, def-wf-middle-extension, ordinary direct-image and
zeroth-derived identification clauses (blueprint: def-wf-middle-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  {U₀ C₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]

/-- The actual base change of the model open immersion to the fixed algebraic closure.
Source: latest blueprint, U and C (blueprint: def-wf-middle-extension). -/
abbrev geometricMap (j₀ : U₀ ⟶ C₀) :
    (D.geometricFiber U₀).left ⟶ (D.geometricFiber C₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left

/-- Model base change commutes with geometric Frobenius.
Source: latest blueprint, induced Weil-structure convention
(blueprint: def-wf-middle-extension).
Proof: compose both sides with the two fibre-product projections. On the model
projection both are j₀ after projection. On the coefficient projection both are
projection followed by inverse q-power Frobenius. Pullback uniqueness gives the square.
This records the canonical structural equality, not an extra assumption on the sheaf. -/
theorem frobeniusSquare (j₀ : U₀ ⟶ C₀) :
    CommSq (D.geometricFrobenius U₀).hom (geometricMap D j₀)
      (geometricMap D j₀) (D.geometricFrobenius C₀).hom := by
  sorry

end WeilConjectures.NativeL2
