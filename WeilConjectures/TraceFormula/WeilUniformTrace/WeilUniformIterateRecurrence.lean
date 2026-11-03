/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.SmoothPurity.GeometricFrobeniusTransport.GeometricFrobeniusCohomologyTransport
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Base value and successor equation for direct compact Weil transport

Source: latest blueprint, det-thm-tf-uniform-formula-weil.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures.WeilUniformTrace

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

/-- The base value and successor recurrence for direct compact Weil transport.
Source: latest blueprint, det-thm-tf-uniform-formula-weil.proof.md, clause (2)
(blueprint: lem-wutf-direct-iterate-recurrence).

Proof: choose a compactification over k₀ by Nagata and base-change it to k. On this
compactification, geometric Frobenius acts on the open, proper, and point terms.
The composition equation for proper/open exchange and point restriction gives
τ_(m+1,K) = H(c_m) τ_(1,P_m K) τ_(m,K), where P_r = L(g_X^r)^* and H = RΓ_c.
The recurrence defining the iterated Weil map is θ_(m+1) = θ P_1(θ_m) c_m⁻¹.
Naturality of τ_1 in θ_m cancels c_m and gives U_(m+1) = U_1 U_m, while θ_1 = θ
identifies U_1 with the recorded globalFrobenius. Use the canonical refinement
comparison to the specified c₀; proper/open exchange and point restriction are
natural in that comparison, so both identities survive conjugation. Apply H^i,
which preserves composites. This proves only the base and successor equations;
the all-power assertion is a separate induction in the importing item. -/
theorem direct_iterate_recurrence
    (c : WeilCoefficient ell)
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ c) (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).map (directIterate D ell hEll X₀ c c₀ K 1) =
      (DerivedCategory.homologyFunctor _ i).map
        (globalFrobenius D ell hEll X₀ c c₀ K) ∧
    ∀ m : ℕ, 1 ≤ m →
      (DerivedCategory.homologyFunctor _ i).map
          (directIterate D ell hEll X₀ c c₀ K (m + 1)) =
        (DerivedCategory.homologyFunctor _ i).map
            (directIterate D ell hEll X₀ c c₀ K m) ≫
          (DerivedCategory.homologyFunctor _ i).map
            (globalFrobenius D ell hEll X₀ c c₀ K) := by
  sorry

end WeilConjectures.WeilUniformTrace
