/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionNorm2

/-!
# Ordinary source and target tensor complexes

Source: Stacks Project, Tags 03EK, 06YU and 0F1J
(blueprint: def-kun-prime-coefficient-complexes-input-output).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
/-- Ordinary source tensor complex.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-complexes-input-output). -/
def primeTensorInputComplex (φ : A →+* B) (V : Scheme.{u})
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) :=
  primeSingleComplex A V M ⊗ primeRestrictedComplex φ V C
/-- Restricted ordinary target tensor complex.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-complexes-input-output). -/
def primeTensorOutputComplex (φ : A →+* B) (V : Scheme.{u})
    (N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B))
    (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) :=
  primeRestrictedComplex φ V (primeSingleComplex B V N ⊗ C)

end AlgebraicGeometry.Etale
