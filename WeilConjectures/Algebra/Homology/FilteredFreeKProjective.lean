/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import WeilConjectures.Algebra.Homology.FilteredFreeKProjectiveStep
import WeilConjectures.Algebra.Homology.FilteredFreeKProjectiveAssembly

/-!
# Filtered free complexes are K-projective

## References

* Stacks Project, Differential Graded Algebra, Tags 09KJ, 09KL and 09KM
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Finite-stage induction for filtered free complexes. -/
theorem isKProjective_of_filtered_free_stage {A : Type u} [CommRing A]
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (step : ∀ n, F n ⟶ F (n + 1))
    (hzero : IsZero (F 0))
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k))
    (hquot : ∀ n, ∃ (I : Type (max u v)) (degree : I → ℤ),
      Nonempty (cokernel (step n) ≅
        ∐ (fun i : I ↦
          (HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) (degree i)).obj
            (ModuleCat.of A (ULift.{v} A))))) :
    ∀ n, (F n).IsKProjective := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun f _ => ⟨Homotopy.ofEq ?_⟩⟩
      exact hzero.eq_of_src f 0
  | succ n ih =>
      apply isKProjective_of_filtered_free_step (step n) ih
      · intro k
        exact hsplit n k
      · exact hquot n

/-- Telescope assembly for an exhaustive split filtration. -/
theorem isKProjective_of_filtered_free_telescope
    {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hzero : IsZero (F 0)) (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : P.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x)
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k))
    (hstage : ∀ n, (F n).IsKProjective) :
    P.IsKProjective :=
  filtered_free_telescope_assembly P F ι step hzero hmono hcompat hexhaustive hsplit hstage


/-- An exhaustive, degreewise split filtration with shifted free quotients is K-projective. -/
theorem isKProjective_of_filtered_free {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hzero : IsZero (F 0)) (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : P.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x)
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k))
    (hquot : ∀ n, ∃ (I : Type (max u v)) (degree : I → ℤ),
      Nonempty (cokernel (step n) ≅
        ∐ (fun i : I ↦
          (HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) (degree i)).obj
            (ModuleCat.of A (ULift.{v} A))))) :
    P.IsKProjective := by
  have hstage' : ∀ n, (F n).IsKProjective :=
    isKProjective_of_filtered_free_stage F step hzero hsplit hquot
  exact isKProjective_of_filtered_free_telescope P F ι step hzero hmono hcompat
    hexhaustive hsplit hstage'

end CochainComplex
