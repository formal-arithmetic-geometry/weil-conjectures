/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteOpenCoverDirectImageSpectralSequence
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-! Finite-cover spectral assembly after evaluation at a coefficient sheaf.

The theorem records the finite-cover construction and its derived-category comparison.  Its
proof is the ordered Cech spectral-sequence construction: evaluate the functorial sequence at the
coefficient object, transport the finite page and abutment filtration through evaluation, and use
the canonical homology comparison for the plus derived functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Etale

universe u

namespace AlgebraicGeometry.Etale

/-- Evaluated finite-cover spectral assembly, including the plus-derived abutment. -/
theorem finite_cover_spectral_object_assembly
    {k : Type (u + 1)} [CommRing k] [Finite k]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : ℕ) (U : Fin m → X.Opens) (hU : iSup U = ⊤)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k))
    (hTerms : ∀ (p r : ℕ) (a : Fin (p + 1) ↪o Fin m),
      Scheme.IsConstructibleSheaf
        ((finiteCoverHigherImage k f (finiteCoverIntersection U a) r).obj M)) :
    ∃ E : E₂CohomologicalSpectralSequenceNat
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} k)),
      (∀ p q : ℕ, Scheme.IsConstructibleSheaf ((E.page 2).X (p, q))) ∧
      E.AbutsTo (fun n : ℕ ↦
        ((lowerStar (ModuleCat.{u + 1} k) f).rightDerived n).obj M) := by
  sorry

end AlgebraicGeometry.Etale
