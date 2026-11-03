/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.FiniteRingTrace.FiniteRingExceptionalComparisons

/-! # Finite-ring product comparison maps

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/
sk-def-sf-kv-maps/def-sf-kv-maps.md,
clauses (i)--(iv), with Wei Yang #1423 (blueprint: thm-trf-kunneth-verdier).
This finite specialization uses precisely the published Ku, alpha, beta and kappa
constructions, and the constructible adjunctions supplied by the current Brown theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing
open AlgebraicGeometry.ProEtale.CondensedRing.ProductComparisons
open scoped CategoryTheory.Obj

namespace WeilConjectures.FiniteRingTrace

/-- The geometric characteristic inequality in the global finite-field convention.
Source: def-sf-kv-maps, standing base convention (blueprint: thm-trf-kunneth-verdier). -/
abbrev geometricCharNe (D : FiniteFieldDatum.{u}) (ell : ℕ) (hell : ell ≠ D.p) :
    ringChar D.k ≠ ell := by
  let := fieldChar D
  exact (ringChar.eq D.k D.p).trans_ne hell.symm

/-- The actual regular coefficient object in its recorded full subcategory.
Source: def-sf-kv-maps (iv), coefficient unit (blueprint: thm-trf-kunneth-verdier). -/
def coefficientUnit (A : Type) [CommRing A] [Finite A] (D : FiniteFieldDatum.{u}) :
    Ctf A (Spec (.of D.k)) :=
  ⟨constantCoefficientObject (coefficient A) (Spec (.of D.k)),
    constantCoefficientObject_mem (coefficient A) (Spec (.of D.k))⟩

end WeilConjectures.FiniteRingTrace
