/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalCompletedLineCompleteAux

/-! # Completeness of a completed-coefficient line

Source: Stacks Tags 099L, 099M and 091Q, and the diagonal trace proof, paragraph (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- A locally free rank-one module over the actual completed Z_l coefficient sheaf
has a derived l-complete underlying constant-coefficient complex in degree zero.

Source: Stacks Tags 099L, 099M and 091Q. -/
theorem diagonalCompletedLine_complete (l : ℕ) [Fact l.Prime] (S : Scheme.{u})
    [IsNoetherian S] [DiagonalTraceLocalizations l S]
    (L : DiagonalCompleted l S) (hL : L.IsFiniteLocallyFreeOfRank 1) :
    ∀ V : DerivedCategory (DiagonalMod l S), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (diagonalCompletedUnderlying l S).obj
        ((DerivedCategory.singleFunctor (DiagonalCompleted l S) 0).obj L)) := by
  have hcover : ∀ U : S.ProEt, ∃ s : Sieve U, s ∈ (Scheme.ProEt.topology S) U ∧
      ∀ (V : S.ProEt) (f : V ⟶ U), s f →
        Nonempty (L.over V ≅
          (SheafOfModules.unit
            (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))).over V) := by
    intro U
    obtain ⟨I, X, hX, h⟩ :=
      (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
        (M := L) (r := 1)).mp hL
    refine ⟨Sieve.ofObjects X U, hX U, ?_⟩
    rintro V f ⟨i, ⟨g⟩⟩
    obtain ⟨e⟩ := h i
    exact ⟨((SheafOfModules.overFunctorMap
      (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)) g).app L).symm ≪≫
      (SheafOfModules.overMap
        (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)) g).mapIso
        (e ≪≫ SheafOfModules.freeUniqueIso _) ≪≫
        SheafOfModules.overMapUnitIso
          (R := Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)) g⟩
  exact diagonalCompletedLine_complete_of_cover l S L hcover

end AlgebraicGeometry.ProEtale.DiagonalTrace
