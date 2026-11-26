/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.RingTheory.MPseudoCoherentLocalizationConeConstruction
import WeilConjectures.RingTheory.MPseudoCoherentLocalizationConeLocal

/-!
# Lowering the cohomology bound in pseudo-coherent localization descent

A finite-free approximation of top cohomology lowers the cohomological upper bound by one while
preserving `m`-pseudo-coherence of every localization; this is the induction step for descending
pseudo-coherence along localizations.

## Implementation details

Local `m`-pseudo-coherence gives finite generation of local degree-`n` cohomology (Stacks 064S),
hence of `Hⁿ(M)` (Stacks 00EO). A finite free module surjecting onto `Hⁿ(M)` gives a chain map
from a single-term complex `E`, and its mapping cone `N` has `Hʲ(N) = 0` for `j > n - 1`. Since
localization is exact and commutes with cones, the first clause of Stacks 064R shows that every
localization of `N` is `m`-pseudo-coherent.

## References

* [Stacks, Tag 066D] (proof, second and third paragraphs)
* [Stacks, Tags 064S, 00EO, 064R]
-/

@[expose] public section

universe w₁ w₂ v₁ u₁

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- A finite-free top-cohomology approximation lowers the bound by one and preserves the
fixed-degree pseudo-coherence of every localization. Only a single induction step is asserted. -/
theorem isMPseudoCoherent_localization_cone_step
    {A : Type u₁} [CommRing A] [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    (M : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
    (r : ℕ) (f : Fin r → A)
    [∀ i : Fin r, HasDerivedCategory.{w₂} (ModuleCat.{max u₁ v₁} (Localization.Away (f i)))]
    (hf : Ideal.span (Set.range f) = ⊤)
    (m n : ℤ) (hmn : m ≤ n)
    (hvan : ∀ j : ℤ, n < j →
      IsZero ((homologyFunctor (ModuleCat.{max u₁ v₁} A) j).obj (Q.obj M)))
    (hlocal : ∀ i : Fin r, IsMPseudoCoherent m
        (Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj M))) :
    ∃ (E N : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
      (a : Q.obj E ⟶ Q.obj M) (b : Q.obj M ⟶ Q.obj N)
      (c : Q.obj N ⟶ (Q.obj E)⟦(1 : ℤ)⟧),
      Triangle.mk a b c ∈ distTriang (DerivedCategory (ModuleCat.{max u₁ v₁} A)) ∧
      IsMPseudoCoherent m (Q.obj E) ∧
      (∀ j : ℤ, n - 1 < j →
        IsZero ((homologyFunctor (ModuleCat.{max u₁ v₁} A) j).obj (Q.obj N))) ∧
      (∀ i : Fin r, IsMPseudoCoherent m
        (Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj N))) := by
  obtain ⟨E, N, a, b, c, hT, hE, hN⟩ :=
    localization_cone_construction M r f hf m n hmn hvan hlocal
  refine ⟨E, N, a, b, c, hT, hE, hN, ?_⟩
  exact localization_cone_local M r f hf m n hmn hvan hlocal E N a b c hT hE hN

end DerivedCategory
