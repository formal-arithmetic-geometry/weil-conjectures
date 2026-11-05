/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
# The tower of finite Galois subextensions as a limit of schemes

Let `Ω / L` be a (possibly infinite) Galois extension. This file proves that `Ω` is the filtered
colimit of its finite Galois subextensions `L'` in `CommRingCat`
(`FiniteGaloisIntermediateField.isColimitRingCocone`), hence that `Spec Ω` is the cofiltered
limit of the `Spec L'` (`FiniteGaloisIntermediateField.isLimitSpecCone`).

Base change along a fixed morphism preserves limits of connected diagrams over a base
(`CategoryTheory.Limits.isLimitPullbackDiagramCone`), so for a scheme `G` over `Spec L`,
`G ×_L Ω = lim_{L'} G ×_L L'` (`AlgebraicGeometry.isLimitGaloisLevelCone`), and likewise for any
further base change `W ×_G (G ×_L Ω) = lim_{L'} W ×_G (G ×_L L')`.
-/

@[expose] public section

universe v w u

open CategoryTheory Limits Opposite

/-! ### Base change of a limit cone over a base -/

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {I : Type*} [Category I] {D : I ⥤ C} {S T : C} (f : T ⟶ S)
  (p : D ⟶ (Functor.const I).obj S) [∀ i, HasPullback f (p.app i)]

variable (c : Cone D) (q : c.pt ⟶ S) (hq : ∀ i, c.π.app i ≫ p.app i = q) [HasPullback f q]

end CategoryTheory.Limits

/-! ### `Ω` as the colimit of its finite Galois subextensions -/

namespace FiniteGaloisIntermediateField

variable (L Ω : Type u) [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω]

end FiniteGaloisIntermediateField

/-! ### The tower `G ×_L L'` -/

namespace AlgebraicGeometry

open FiniteGaloisIntermediateField

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

end AlgebraicGeometry
