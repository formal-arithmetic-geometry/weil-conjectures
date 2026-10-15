/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso

/-! # K-flat complexes with an independent coefficient universe

The tensor product is the same sheafified tensor product as in `KFlat`. Relative
essential smallness permits the coefficient universe to differ from both site universes.
-/

@[expose] public section

universe u v w

open CategoryTheory MonoidalCategory Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})

/-- Tensor localization is monoidal after transporting the site to its small model in
the coefficient universe. Source: Stacks Project, Modules on Sites, Section 03EK. -/
theorem isMonoidal_W_independentCoefficients :
    (J.W.inverseImage (PresheafOfModules.toPresheaf.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).IsMonoidal := by
  sorry

/-- Tensoring a zero morphism on the left is zero for module sheaves over a relatively
small site. Source: Stacks Project, Cohomology on Sites, Tag 06YN. -/
theorem preservesZeroMorphisms_curriedTensor_independentCoefficients :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    (curriedTensor (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))).PreservesZeroMorphisms := by
  sorry

/-- Tensoring a zero morphism on the right is zero, by symmetry of the tensor product.
Source: Stacks Project, Cohomology on Sites, Tag 06YN. -/
theorem preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (M : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    let T := curriedTensor (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (T.obj M).PreservesZeroMorphisms := by
  sorry

end SheafOfModules

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}

set_option synthInstance.maxSize 256 in
/-- K-flatness against every acyclic complex, using the sheafified total tensor complex
at an independent coefficient universe. Source: Stacks Project, Tag 06YN. -/
def IsKFlatIndependentCoefficients
    (K : CochainComplex (SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) : Prop :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  ∀ F : CochainComplex (SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ,
    F.Acyclic → (mapBifunctor F K (curriedTensor _)).Acyclic

/-- A quasi-isomorphism from a K-flat complex, with independent coefficient and site
universes. Source: Stacks Project, Tag 06YS. -/
def IsKFlatResolutionIndependentCoefficients
    {K G : CochainComplex (SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ}
    (f : K ⟶ G) : Prop :=
  QuasiIso f ∧ K.IsKFlatIndependentCoefficients

/-- In the live K-flat universe, the independent predicate is the live predicate.
The two definitions use the same total tensor and differ only in how its instances
are supplied. -/
theorem isKFlatIndependentCoefficients_iff_isKFlat
    {C : Type u} [Category.{v} C] [EssentiallySmall.{max u v} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{max u v}}
    (K : CochainComplex (SheafOfModules.{max u v} ((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ) :
    IsKFlatIndependentCoefficients K ↔ IsKFlat K := by
  sorry

/-- The independent resolution predicate specializes to the live resolution predicate
when the coefficient universe is the maximum of the site universes. -/
theorem isKFlatResolutionIndependentCoefficients_iff_isKFlatResolution
    {C : Type u} [Category.{v} C] [EssentiallySmall.{max u v} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{max u v}}
    {K G : CochainComplex (SheafOfModules.{max u v} ((sheafCompose J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (f : K ⟶ G) :
    IsKFlatResolutionIndependentCoefficients f ↔ IsKFlatResolution f := by
  sorry

end CochainComplex
