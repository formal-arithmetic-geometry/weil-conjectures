/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories
public import Sheaf.AlgebraicGeometry.HypercohomologyFiltrations
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.TruncationHypercohomology
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact

/-!
# Bounded-below truncation criterion

Source: blueprint sec-smooth-base-change/sk-rem-rest,
node sbc-lem-bounded-below-truncation-criterion, order 1439
(blueprint: sbc-lem-bounded-below-truncation-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Canonical truncation above n does not change the degree-n cohomology of the three
hypercohomology functors. In each truncation spectral sequence all terms above q = n
on the degree-n diagonal vanish, on every page starting at E₂. The support assertion
is expressed on every bounded-below representative of K, so involves no choice of resolution.
Source: blueprint sec-smooth-base-change/sk-rem-rest, order 1439
(blueprint: sbc-lem-bounded-below-truncation-criterion).

Proof:
1. Choose a lower cohomology bound a and a representative vanishing below a, using
   def-sbc-standard-tstructure-derived-category. The three spectral sequences of
   def-weil-pbc-hypercohomology-filtrations have p ≥ 0; hence p + q = n forces q ≤ n.
   This remains true on later pages, which are subquotients of the preceding pages.
2. Apply part 5 of thm-sp-truncation-e2 to g_*: its canonical map c_n is invertible.
   The substitutions in def-sp-etale-dictionary identify this with the first map here.
3. prop-weil-pbc-inverse-image-exact and lem-weil-pbc-exact-functor-bounded-below
   identify the second map with f⁻¹ applied to the first, hence it is invertible.
4. Exactness of e⁻¹ identifies its termwise image of the canonical truncation and
   inclusion with those of e⁻¹K. Apply part 5 of thm-sp-truncation-e2 to h_* to get
   invertibility of the third map. No torsion-preservation hypothesis is needed. -/
theorem boundedBelow_truncation_criterion
    {Y T X S : Scheme.{u}} (g : T ⟶ S) (f : X ⟶ S) (e : Y ⟶ T) (h : Y ⟶ X)
    (_sq : ChosenCartesianSquare e h g f) (P : Set ℕ)
    (K : AbelianDerivedCategoryPlusTorsionOfPrimes T P) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((hypercohomologyFirstFunctor g).map
        ((DerivedCategory.TStructure.t.truncLEι n).app K.obj))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((hypercohomologyBaseChangeFunctor g f).map
        ((DerivedCategory.TStructure.t.truncLEι n).app K.obj))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((hypercohomologySecondFunctor h e).map
        ((DerivedCategory.TStructure.t.truncLEι n).app K.obj))) ∧
    (∀ L : CochainComplex.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}),
      Nonempty (DerivedCategory.Q.obj L.obj ≅ K.obj) →
      ∀ (r : ℕ) (q : ℤ), 2 ≤ r → n < q →
        IsZero ((hypercohomologyCouple (hypercohomologyFirstFunctor g) L).page r (n - q) q) ∧
        IsZero ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor g f) L).page
          r (n - q) q) ∧
        IsZero ((hypercohomologyCouple (hypercohomologySecondFunctor h e) L).page
          r (n - q) q)) := by
  sorry

end AlgebraicGeometry.Etale
