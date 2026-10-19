/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Splitting a complex with projective cohomology

Source: Stacks Project, proetale.tex, Tag 09C3, cycle-lifting argument
(blueprint: lem-sf-projective-homology-zero-differential-model).
-/

@[expose] public section
set_option autoImplicit false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Projective cohomology can be lifted to cycles, giving a quasi-isomorphism
from the graded cohomology with zero differential.

Source: Stacks Project, proetale.tex, Tag 09C3, cycle-lifting argument
(blueprint: lem-sf-projective-homology-zero-differential-model).

Proof: split the epimorphism from cycles onto cohomology by projectivity in each
integer degree. Compose each splitting with the cycles inclusion. These maps form
a chain map from the zero-differential graded cohomology. On cohomology the map is
the identity, so it is a quasi-isomorphism. No boundedness assumption is required. -/
theorem exists_zero_differential_model_of_projective_homology
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (hK : ∀ q : ℤ, Projective (K.homology q)) :
    ∃ (P : CochainComplex C ℤ) (f : P ⟶ K),
      (∀ q : ℤ, P.X q = K.homology q) ∧
      (∀ i j : ℤ, P.d i j = 0) ∧ QuasiIso f := by
  let P : CochainComplex C ℤ := { X := fun q ↦ K.homology q, d := fun _ _ ↦ 0 }
  have (q : ℤ) : Projective (K.homology q) := hK q
  let s (q : ℤ) : K.homology q ⟶ K.cycles q :=
    Projective.factorThru (𝟙 _) (K.homologyπ q)
  have hs (q : ℤ) : s q ≫ K.homologyπ q = 𝟙 _ := Projective.factorThru_comp _ _
  let f : P ⟶ K :=
    { f q := s q ≫ K.iCycles q
      comm' i j _ := by simp only [P, zero_comp, Category.assoc,
        K.iCycles_d, comp_zero] }
  refine ⟨P, f, fun _ ↦ rfl, fun _ _ ↦ rfl, ?_⟩
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hc : IsIso (P.iCycles q) := P.isIso_iCycles q (q + 1) (by simp) rfl
  have hp : IsIso (P.homologyπ q) := P.isIso_homologyπ (q - 1) q (by simp) rfl
  have hcycles : HomologicalComplex.cyclesMap f q = P.iCycles q ≫ s q := by
    apply (cancel_mono (K.iCycles q)).mp
    rw [HomologicalComplex.cyclesMap_i]
    exact (Category.assoc _ _ _).symm
  have he : P.homologyπ q ≫ HomologicalComplex.homologyMap f q = P.iCycles q := by
    rw [HomologicalComplex.homologyπ_naturality, hcycles, Category.assoc, hs,
      Category.comp_id]
  have : IsIso (P.homologyπ q ≫ HomologicalComplex.homologyMap f q) := he ▸ hc
  exact IsIso.of_isIso_comp_left (P.homologyπ q) _

end CochainComplex
