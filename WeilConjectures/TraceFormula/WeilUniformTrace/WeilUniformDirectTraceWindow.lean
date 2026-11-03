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

/-! # Direct-transport uniform trace identity on a common cohomology window

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

/-- The uniform formula for direct m-fold transport on a common vanishing window.
Source: latest blueprint, det-thm-tf-uniform-formula-weil.proof.md, clause (2)
(blueprint: lem-wutf-direct-trace-window).

Proof: view the rational strict condensed pair as a pair for the general uniform
formula using Dctf = Dbc. Its m-fold global operator is compact-support pullback
transport followed by the iterated Weil map; the proper/open and terminal-section
comparisons identify this operator with directIterate on compactComplex. Its local
operator is the same iterated map after geometric-point reparametrization; derived
pullback composition and point_return identify it with localFrobenius. Apply the
uniform formula with these identifications. Its perfect complexes admit the
cohomological trace formula over the coefficient field, identified with Γ by
constant sections. Thus its categorical traces are alternating cohomology traces.
All degrees outside s vanish by hC and hS; the trace on a zero module is zero.
Restrict the integer sums to s, adding any zero terms inside s. The integer sign
is exactly i.negOnePow. This gives the displayed equation for the direct operator,
without identifying that operator with a power of the one-step Frobenius and
without asserting cohomology finiteness or producing a vanishing window. -/
theorem direct_trace_window
    (c : WeilCoefficient ell)
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ c) (m : ℕ) (hm : 1 ≤ m)
    (s : Finset ℤ)
    (hC : ∀ i : ℤ, i ∉ s → IsZero (compactCohomology D ell hEll X₀ c c₀ K i))
    (hS : ∀ (y : D.extensionPoints X₀ m hm) (i : ℤ), i ∉ s →
      IsZero (stalkCohomology D ell hEll X₀ c K m hm y i)) :
      (∑ i ∈ s, (i.negOnePow : ℤ) • cohomologyTrace c
        (compactComplex D ell hEll X₀ c c₀ K) (directIterate D ell hEll X₀ c c₀ K m) i) =
      ∑ᶠ y : D.extensionPoints X₀ m hm,
        ∑ j ∈ s, (j.negOnePow : ℤ) • cohomologyTrace c
          (stalkComplex D ell hEll X₀ c K m hm y)
          (localFrobenius D ell hEll X₀ c K m hm y) j := by
  sorry

end WeilConjectures.WeilUniformTrace
