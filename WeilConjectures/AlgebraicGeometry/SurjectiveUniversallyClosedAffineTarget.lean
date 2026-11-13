/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveAffineTarget
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed
import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FinitePresentationApproximation

/-! # Affine target of a surjective universally closed morphism

## References

* [Stacks Project, Tag 05YU](https://stacks.math.columbia.edu/tag/05YU)
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry

/-- A scheme receiving a surjective universally closed morphism from an affine scheme is affine.
-/
theorem isAffine_of_surjective_of_universallyClosed {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [Surjective f] [UniversallyClosed f] : IsAffine Y := by
  have hsep : IsSeparated (Limits.terminal.from Y) :=
    isSeparated_of_surjective_universallyClosed (Limits.terminal.from X) (Limits.terminal.from Y) f
      (Limits.terminal.comp_from f)
  have : Y.IsSeparated := ⟨hsep⟩
  have : IsAffineHom (f ≫ Limits.terminal.from Y) := by
    rw [Limits.terminal.comp_from]
    infer_instance
  have : IsAffineHom f := IsAffineHom.of_comp f (Limits.terminal.from Y)
  have : IsIntegralHom f :=
    (IsIntegralHom.iff_universallyClosed_and_isAffineHom).mpr ⟨inferInstance, inferInstance⟩
  have : CompactSpace Y := f.surjective.compactSpace f.continuous
  obtain ⟨F, _⟩ := f.exists_finiteApproximation_of_isIntegralHom
  obtain ⟨i, hi⟩ := Scheme.exists_isAffine_of_isLimit F.D (Limits.Cone.mk X F.π) F.isLimit
  let := hi
  have : Surjective (F.π.app i ≫ F.p i) := by
    rw [F.π_p]
    infer_instance
  have : Surjective (F.p i) := Surjective.of_comp (F.π.app i) (F.p i)
  exact isAffine_of_isFinite_surjective (F.p i)

end AlgebraicGeometry
