/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Algebra.Homology.AbelianVariety.UniversalH0SplitFactorization

/-!
# A generalized inverse for the first differential

Universal rank-one zeroth homology makes the first differential a split map onto its image.

## References

* Stacks Project, Tags 00O0 and 00NX (fixed-affine adaptation)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Universal rank-one zeroth homology makes the first differential a split map onto
its image, with the image a direct summand of the next term. -/
theorem universalH0_split_differential
    (R : Type v) [CommRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hf0 : Module.Finite R (P.X 0))
    (hf1 : Module.Finite R (P.X 1))
    (hp0 : Module.Projective R (P.X 0))
    (hp1 : Module.Projective R (P.X 1))
    (hneg : IsZero (P.X (-1)))
    (hzero : ∀ (B : Type v) [CommRing B] (φ : R →+* B),
      let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
      Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) :
    ∃ s : P.X 1 ⟶ P.X 0, P.d 0 1 ≫ s ≫ P.d 0 1 = P.d 0 1 := by
  obtain ⟨I, e, p, r, q, hfac, her, hpq⟩ :=
    universalH0_split_factorization R P hf0 hf1 hp0 hp1 hneg hzero
  refine ⟨q ≫ r, ?_⟩
  calc
    P.d 0 1 ≫ (q ≫ r) ≫ P.d 0 1 = (e ≫ p) ≫ (q ≫ r) ≫ e ≫ p := by rw [hfac]
    _ = e ≫ (p ≫ q) ≫ r ≫ e ≫ p := by simp only [Category.assoc]
    _ = e ≫ r ≫ e ≫ p := by simp only [hpq, Category.id_comp]
    _ = P.d 0 1 := by
      rw [← Category.assoc r e p, her, Category.id_comp, ← hfac]
end CochainComplex
