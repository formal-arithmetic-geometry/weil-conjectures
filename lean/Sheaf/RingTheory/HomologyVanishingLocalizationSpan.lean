/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Detecting cohomology vanishing on a finite standard-open cover

Source: Stacks Project, Tag 066D, proof, first paragraph, and Tag 00EO (1).
-/

@[expose] public section

universe w₁ w₂ v₁ u₁

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- Localization at a unit-ideal generating family detects vanishing of one cohomology module.
Source: Stacks Project, Tag 066D, proof, first paragraph, using Algebra, Tag 00EO (1).
(blueprint: lem-pc-homology-vanishing-localization-span).

Proof: Localization is exact, so the homology of the termwise extension of scalars is
canonically the localization of the homology of `M`. Thus the hypothesis says that every
localization of `Hⁿ(M)` at an `f i` is zero. For an element `x` of `Hⁿ(M)`, the zero criterion
for localized modules gives exponents `e i` with `(f i) ^ (e i)` annihilating `x`. The powers
still generate the unit ideal: the radical of their ideal contains every `f i`, and hence
contains 1. Express 1 as a linear combination of these powers and act on `x`, obtaining
`x = 0`. Hence `Hⁿ(M)` is a zero object. The empty family forces the zero ring and the
same conclusion. -/
theorem homology_vanishes_of_localization_span
    {A : Type u₁} [CommRing A] [HasDerivedCategory.{w₁} (ModuleCat.{max u₁ v₁} A)]
    (M : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)
    (r : ℕ) (f : Fin r → A)
    [∀ i : Fin r, HasDerivedCategory.{w₂} (ModuleCat.{max u₁ v₁} (Localization.Away (f i)))]
    (hf : Ideal.span (Set.range f) = ⊤)
    (n : ℤ)
    (hlocal : ∀ i : Fin r,
      IsZero ((homologyFunctor (ModuleCat.{max u₁ v₁} (Localization.Away (f i))) n).obj
        (Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
          (ComplexShape.up ℤ)).obj M)))) :
    IsZero ((homologyFunctor (ModuleCat.{max u₁ v₁} A) n).obj (Q.obj M)) := by sorry

end DerivedCategory
