/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Complements on morphisms locally of finite type

We show that the spectrum of a `ℤ`-algebra of finite type is locally of finite type over
`Spec ℤ` (`AlgebraicGeometry.locallyOfFiniteType_specULiftZIsTerminal_from`), and that the
sections over an affine open of a scheme locally of finite type over `Spec ℤ` form a
finitely generated `ℤ`-algebra
(`AlgebraicGeometry.IsAffineOpen.algebra_finiteType_of_locallyOfFiniteType`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The spectrum of a `ℤ`-algebra of finite type is locally of finite type over `Spec ℤ`. -/
instance locallyOfFiniteType_specULiftZIsTerminal_from (R : Type u) [CommRing R]
    [Algebra.FiniteType ℤ R] :
    LocallyOfFiniteType (specULiftZIsTerminal.from (Spec <| .of R)) := by
  have hfin : RingHom.FiniteType ((algebraMap ℤ R).comp (ULift.ringEquiv (R := ℤ)).toRingHom) :=
    (RingHom.finiteType_algebraMap.mpr ‹_›).comp
      (RingHom.FiniteType.of_surjective _ ULift.ringEquiv.surjective)
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      ((algebraMap ℤ R).comp (ULift.ringEquiv (R := ℤ)).toRingHom))) :=
    HasRingHomProperty.Spec_iff.mpr hfin
  rwa [specULiftZIsTerminal.hom_ext (specULiftZIsTerminal.from _) (Spec.map _)]

/-- The sections over an affine open of a scheme locally of finite type over `Spec ℤ` form
a finitely generated `ℤ`-algebra. -/
theorem IsAffineOpen.algebra_finiteType_of_locallyOfFiniteType {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))} [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  set φ := f.appLE ⊤ U (by simp) with hφdef
  have hft : RingHom.FiniteType φ.hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  rw [← RingHom.finiteType_algebraMap,
    Subsingleton.elim (algebraMap ℤ Γ(X, U))
      ((φ.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).inv.hom).comp
        (ULift.ringEquiv (R := ℤ)).symm.toRingHom)]
  refine (hft.comp (RingHom.FiniteType.of_surjective _ ?_)).comp
    (RingHom.FiniteType.of_surjective _ (ULift.ringEquiv (R := ℤ)).symm.surjective)
  exact (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).symm.commRingCatIsoToRingEquiv.surjective

end AlgebraicGeometry
