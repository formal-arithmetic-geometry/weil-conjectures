/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedLisseDualityDefs
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.DeligneLaumon.CondensedLisseDualOperations
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SecSmoothPurity.TransportLinePull
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.DeligneLaumon.FiniteToCondensedSmoothAdjunctionTransport

import WeilConjectures.DeligneLaumon.CondensedLisseNormalizedPurity
import WeilConjectures.DeligneLaumon.CondensedLisseCohomologyFormula
import WeilConjectures.DeligneLaumon.CondensedLisseOpenDualizing
import WeilConjectures.DeligneLaumon.CondensedLisseRestriction

/-! # Lisse dual cohomology with condensed coefficients

Source: latest blueprint, thm-a1-curve-perverse-heart.proof.md, Step 2
(blueprint: lem-per-condensed-lisse-dual-cohomology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseDual

variable (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell)

/-- Lisse dual cohomology and open restriction with condensed coefficients over
an arbitrary perfect field, including characteristic zero.

Source: latest blueprint, thm-a1-curve-perverse-heart.proof.md, Step 2
(blueprint: lem-per-condensed-lisse-dual-cohomology).

Proof:
1. Apply the existing finite/general-field adjunction transport at the coefficient
   unit. The proved coefficient-unit membership supplies its bounded finite-Tor
   hypothesis. Evaluating the counit-compatible transport gives actual localizing
   right adjoints and the finite-system-normalized purity witnesses; this is
   normalized_purity_exists.
2. Apply lisse_cohomology_formula to those same adjoints and purity witnesses.
   Its bounded calculation constructs the natural reversed-cohomology formula and
   the square for every normalized open orientation. Ordinary lisse duality and
   local unit bases for Tate powers then prove lisse preservation and vanishing
   equivalence, by cohomology_lisse_vanishing.
3. The individual root-normalized shifted Tate maps are constructed in
   open_line_normalized_exists; open_line_coherence supplies their composition.
   Conjugate those maps by the chosen purity isomorphisms. Functoriality cancels
   the middle purity and its inverse, proving open normalization and composition
   for dualizing objects, by open_dualizing_exists. Empty schemes are included.
4. The proved native open internal-Hom comparison is invertible for all complexes.
   Transport it along the total-versus-exact monoidal comparison and the chosen
   dualizing-object isomorphism; its naturality supplies OpenNaturality. The
   independent open_lisse lemma proves lisse preservation of exact inverse image.
5. Evaluate the cohomology square from Step 2 at exactly the open orientation
   constructed in Step 3. Assemble all clauses with these unchanged witnesses.
-/
theorem condensed_lisse_dual_cohomology (k : Type u) [Field k] [PerfectField k]
    (_hEll : IsUnit (ell : k)) : Comparisons ell PurityTransport.Coefficient.closure k := by
  obtain ⟨A, p, hn⟩ := normalized_purity_exists ell k _hEll
  obtain ⟨cohom, he⟩ := lisse_cohomology_formula ell k _hEll A p
  obtain ⟨hl, hv⟩ := cohomology_lisse_vanishing ell .closure _hEll A cohom
  obtain ⟨e, hen, hec⟩ := open_dualizing_exists ell .closure _hEll A p
  obtain ⟨hi, hnat⟩ := open_restriction ell .closure A e
  exact ⟨A, p, hn, cohom, hl, hv, e, hen, hec,
    open_lisse ell .closure, hi, hnat, he e hen⟩

end AlgebraicGeometry.ProEtale.CondensedLisseDual
