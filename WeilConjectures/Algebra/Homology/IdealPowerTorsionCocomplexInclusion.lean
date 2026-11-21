/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.IdealPowerTorsionFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Inclusion of the ideal-power torsion subcomplex

## References

* Stacks Project, Tags 0BJA and 0A6T
-/

@[expose] public section

universe u
open CategoryTheory

namespace ModuleCat

/-- The degreewise subtype inclusions form the inclusion of the torsion subcomplex. -/
def idealPowerTorsionCocomplexι {R : Type u} [CommRing R] (J : Ideal R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    ((idealPowerTorsion J).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ K where
  f n := ModuleCat.ofHom (Ideal.primaryComponent (K.X n) J).subtype
  comm' i j _ := by
    ext x
    rfl

/-- Each component of the torsion inclusion is monic. -/
instance idealPowerTorsionCocomplexι_f_mono {R : Type u} [CommRing R] (J : Ideal R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    Mono ((idealPowerTorsionCocomplexι J K).f n) := by
  apply ConcreteCategory.mono_of_injective
  exact Subtype.val_injective

/-- The torsion subcomplex inclusion is monic. -/
instance idealPowerTorsionCocomplexι_mono {R : Type u} [CommRing R] (J : Ideal R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    Mono (idealPowerTorsionCocomplexι J K) :=
  HomologicalComplex.mono_of_mono_f _ (fun _ ↦ inferInstance)

end ModuleCat
