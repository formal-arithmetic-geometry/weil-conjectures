/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import WeilConjectures.Algebra.Homology.FreeCoverBicomplex
import WeilConjectures.Algebra.Homology.TotalFreeFiltration
import WeilConjectures.AlgebraicGeometry.DerivedTotalResolutionQuasiIso

/-!
# Filtered free resolutions of cochain complexes

## References

* Stacks Project, Differential Graded Algebra, Lemma 15.60.9 (Tag 09KP)
* Stacks Project, More on Algebra, Remark 15.60.11 (Tag 09PB)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Every complex `M` of modules over a commutative ring `A` receives a quasi-isomorphism from a
complex `P` with an exhaustive filtration by subcomplexes, indexed by natural numbers with
`F 0 = 0`. Each step is split in every degree, and each quotient is a direct sum of copies of
`A` concentrated in integer degrees. -/
theorem exists_filtered_free_resolution {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (q : P ⟶ M),
      QuasiIso q ∧
      ∃ (F : ℕ → CochainComplex (ModuleCat.{u} A) ℤ)
        (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1)),
        IsZero (F 0) ∧
        (∀ n, Mono (ι n)) ∧
        (∀ n, step n ≫ ι (n + 1) = ι n) ∧
        (∀ (k : ℤ) (x : P.X k), ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x) ∧
        (∀ (n : ℕ) (k : ℤ),
          ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
            (step n).f k ≫ r = 𝟙 ((F n).X k)) ∧
        (∀ n, ∃ (I : Type u) (degree : I → ℤ),
          Nonempty (cokernel (step n) ≅
            ∐ (fun i : I =>
              (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (degree i)).obj
                (ModuleCat.of A A)))) := by
  obtain ⟨K, ε, a, hpos, hε₀, hεneg, hex, hex₀, hsurj, hcyc, hcyc₀, hcycsurj,
    hcols⟩ := exists_freeCoverBicomplex M
  refine ⟨K.total (ComplexShape.up ℤ), ε, ?_, ?_⟩
  · exact WeilConjectures.DerivedTotalResolution.total_resolution_quasiIso M K ε a
      hpos hε₀ hεneg hex hex₀ hsurj hcyc hcyc₀ hcycsurj
  · exact exists_totalFreeFiltration K hpos hcols

end CochainComplex
