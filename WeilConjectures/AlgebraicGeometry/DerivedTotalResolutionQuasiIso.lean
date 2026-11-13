/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.AlgebraicGeometry.DerivedTotalResolutionHomologyInjective
import WeilConjectures.AlgebraicGeometry.DerivedTotalResolutionHomologySurjective

/-!
# Quasi-isomorphism from a good total resolution

Source: Stacks Project, `literature/stacks-project/homology.tex`,
Lemma 12.19.4 (Tag 09IZ), statement.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace WeilConjectures

namespace DerivedTotalResolution

variable {R : Type u} [Ring R]

set_option linter.unusedVariables false in
/-- The total complex of an exact augmented resolution of cochain complexes is
quasi-isomorphic to the resolved complex (Stacks, Tag 09IZ).

The nonpositive horizontal columns of `K` are the resolution, with column
`-i` representing `Aᵢ`. Positive columns vanish, and `ε` is the augmentation on column zero
and vanishes on negative columns. -/
theorem total_resolution_quasiIso
    (M : CochainComplex (ModuleCat R) ℤ)
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (ε : K.total (ComplexShape.up ℤ) ⟶ M)
    (a : K.X 0 ⟶ M)
    [∀ i, (K.total (ComplexShape.up ℤ)).HasHomology i]
    [∀ i, M.HasHomology i]
    [∀ p q, (K.X p).HasHomology q]
    (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (h_augmentation_zero : ∀ q : ℤ,
      K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp) ≫ ε.f q = a.f q)
    (h_augmentation : ∀ (p q n : ℤ)
      (hp : p < 0) (h : ComplexShape.π (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      K.ιTotal (ComplexShape.up ℤ) p q n h ≫ ε.f n = 0)
    (h_exact : ∀ (p q : ℤ), p < -1 →
      Function.Exact
        ((K.d p (p + 1)).f q).hom
        ((K.d (p + 1) (p + 2)).f q).hom)
    (h_exact_zero : ∀ q : ℤ, Function.Exact
      ((K.d (-1) 0).f q).hom
      (a.f q).hom)
    (h_surjective : ∀ q : ℤ, Function.Surjective
      (a.f q).hom)
    (h_cycles : ∀ (p q : ℤ), p < -1 →
      Function.Exact
        (HomologicalComplex.cyclesMap (K.d p (p + 1)) q).hom
        (HomologicalComplex.cyclesMap (K.d (p + 1) (p + 2)) q).hom)
    (h_cycles_zero : ∀ q : ℤ, Function.Exact
      (HomologicalComplex.cyclesMap (K.d (-1) 0) q).hom
      (HomologicalComplex.cyclesMap a q).hom)
    (h_cycles_surjective : ∀ q : ℤ, Function.Surjective
      (HomologicalComplex.cyclesMap a q).hom) :
    QuasiIso ε := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact ⟨total_resolution_homology_injective M K ε a n h_positive h_augmentation_zero
    h_augmentation h_exact h_exact_zero h_surjective h_cycles h_cycles_zero
    h_cycles_surjective,
    total_resolution_homology_surjective M K ε a n h_positive h_augmentation_zero
      h_cycles_surjective⟩

end DerivedTotalResolution

end WeilConjectures
