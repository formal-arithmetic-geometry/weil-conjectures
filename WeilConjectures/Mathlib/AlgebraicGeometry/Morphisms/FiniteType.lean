/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Sections of schemes of finite type over `Spec ℤ`

We show that the sections over an affine open of a scheme locally of finite type over `Spec ℤ`
form a finitely generated `ℤ`-algebra
(`AlgebraicGeometry.IsAffineOpen.algebra_finiteType_of_locallyOfFiniteType`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The sections over an affine open of a scheme of finite type over `Spec ℤ` form a
finitely generated `ℤ`-algebra. -/
theorem IsAffineOpen.algebra_finiteType_of_locallyOfFiniteType {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))} [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  have hft : RingHom.FiniteType (f.appLE ⊤ U (by simp)).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  rw [← RingHom.finiteType_algebraMap,
    Subsingleton.elim (algebraMap ℤ Γ(X, U))
      (((f.appLE ⊤ U (by simp)).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).inv.hom).comp
        (ULift.ringEquiv (R := ℤ)).symm.toRingHom)]
  refine (hft.comp (RingHom.FiniteType.of_surjective _ ?_)).comp
    (RingHom.FiniteType.of_surjective _ (ULift.ringEquiv (R := ℤ)).symm.surjective)
  exact (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).symm.commRingCatIsoToRingEquiv.surjective

end AlgebraicGeometry
