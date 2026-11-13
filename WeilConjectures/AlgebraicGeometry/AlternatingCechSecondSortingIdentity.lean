/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
public import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.AlgebraicGeometry.AlternatingCechSortedContraction
import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingBoundaryTransport
import WeilConjectures.AlgebraicGeometry.AlternatingCechFirstSortingIdentity
import WeilConjectures.CategoryTheory.SiteCechComplex

/-!
# The second Čech sorting identity

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The repeated-tuple operator contracts stable sorting minus alternating projection
(Stacks, Tag 01FM). -/
theorem cechSecondSortingIdentity (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ) :
    (Homotopy.nullHomotopicMap' (cechSecondSortingFamily X U F S)).f p =
      cechStableSortingMap X U F S p - cechAlternatingProjectionMap X U F S p := by
  classical
  apply AddCommGrpCat.ext
  intro s
  funext t
  rw [cechSortingBoundaryTransport X U F S p s t]
  change _ = (cechStableSortingMap X U F S p) s t -
    (cechAlternatingProjectionMap X U F S p) s t
  change _ = (∑ σ : Equiv.Perm (Fin (p + 1)),
    if cechStableSort t σ then
      (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op (s (t ∘ σ)) else 0) -
    (∑ σ : Equiv.Perm (Fin (p + 1)),
    if StrictMono (t ∘ σ) then
      (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap t σ).op (s (t ∘ σ)) else 0)
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  have hs : StrictMono (t ∘ σ) → cechStableSort t σ := by
    intro h
    refine ⟨h.monotone, ?_⟩
    intro i j hij he
    exact (ne_of_lt (h hij) he).elim
  by_cases hsort : cechStableSort t σ
  · rw [ite_eq_left hsort, cechSortedContraction X U F S p s (t ∘ σ) hsort.1]
    by_cases hstrict : StrictMono (t ∘ σ)
    · simp [hsort, hstrict]
    · simp [hsort, hstrict]
  · have hstrict : ¬ StrictMono (t ∘ σ) := fun h ↦ hsort (hs h)
    simp [hsort, hstrict]

end AlgebraicGeometry.Scheme
