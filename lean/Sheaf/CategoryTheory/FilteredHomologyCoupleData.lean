/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# The homology exact couple of a filtered cochain complex

Source: Stacks Project, Tags 012K and 011Q, the homology exact-couple construction.
(blueprint: def-sp-filtered-homology-couple-data).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The short exact sequence of a filtration step and its graded quotient.
Source: Stacks Project, Tag 012K, successive filtration steps.
(blueprint: def-sp-filtered-homology-couple-data). -/
theorem filteredStep_shortExact (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p : ℤ) :
    (ShortComplex.mk
      (Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega)))
      (F.complexQuotientπ p (p + 1) (by omega))
      (cokernel.condition _)).ShortExact := by
  dsimp [DecreasingFiltration.complexQuotientπ, DecreasingFiltration.complexQuotient]
  exact { exact := ShortComplex.exact_cokernel _ }

/-- Filtration-step homology. Source: Stacks, Tag 012K.
(blueprint: def-sp-filtered-homology-couple-data). -/
noncomputable abbrev filteredHomologyD (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (P Q : ℤ) : C := (F.step (-Q) : CochainComplex C ℤ).homology (P + Q)

/-- Graded-piece homology. Source: Stacks, Tag 012K.
(blueprint: def-sp-filtered-homology-couple-data). -/
noncomputable abbrev filteredHomologyE (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (P Q : ℤ) : C := (F.gradedPiece (-Q)).homology (P + Q)

/-- Homology of the filtration inclusion. Source: Stacks, Tag 012K.
(blueprint: def-sp-filtered-homology-couple-data). -/
noncomputable def filteredHomologyAlpha (K : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (P Q : ℤ) :
    filteredHomologyD K F P Q ⟶ filteredHomologyD K F (P - 1) (Q + 1) :=
  HomologicalComplex.homologyMap
    (Subobject.ofLE (F.step (-Q)) (F.step (-(Q + 1)))
      (F.antitone_step (by omega))) (P + Q) ≫
    eqToHom (congrArg (fun n ↦
      (F.step (-(Q + 1)) : CochainComplex C ℤ).homology n) (by omega))

/-- The successive-step connecting map. Source: Stacks, Tags 012K and 011Q.
(blueprint: def-sp-filtered-homology-couple-data). -/
noncomputable def filteredHomologyF (K : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (P Q : ℤ) :
    filteredHomologyE K F P Q ⟶ filteredHomologyD K F (P + 2) (Q - 1) :=
  (filteredStep_shortExact K F (-Q)).δ (P + Q) (P + Q + 1)
    rfl ≫
    eqToHom (congrArg₂ (fun p n ↦ (F.step p : CochainComplex C ℤ).homology n)
      (show -Q + 1 = -(Q - 1) by omega)
      (show P + Q + 1 = P + 2 + (Q - 1) by omega))

/-- Homology of the graded projection. Source: Stacks, Tag 012K.
(blueprint: def-sp-filtered-homology-couple-data). -/
noncomputable def filteredHomologyG (K : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (P Q : ℤ) :
    filteredHomologyD K F P Q ⟶ filteredHomologyE K F (P + (0 : ℕ)) (Q - (0 : ℕ)) :=
  HomologicalComplex.homologyMap
    (F.complexQuotientπ (-Q) (-Q + 1) (by omega)) (P + Q) ≫
    eqToHom (by simp [filteredHomologyE]; rfl)

end CategoryTheory
