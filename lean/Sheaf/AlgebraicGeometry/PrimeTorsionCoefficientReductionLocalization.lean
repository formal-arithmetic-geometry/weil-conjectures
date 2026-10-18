/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionTermwise

/-!
# Localization compatibility for prime coefficient tensor maps

Source: Stacks Project, Tag 0F1J (blueprint: def-kun-prime-coefficient-localization-compatibility).
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

/-- The localized termwise map is the canonical quotient tensor map after Q.
Each typed arrow is fixed by heterogeneous equality to the recorded canonical arrow.
These equalities expose the endpoints without unfolding the localization tensor in
kernel conversion; the final equality is the original localization diagram.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-localization-compatibility). -/
def PrimeTensorLocalizationCompatibility (φ : A →+* B) (V : Scheme.{u})
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B))
    (_q : M ⟶ (Sheaf.restrictScalars V.smallEtaleTopology φ).obj N)
    (D : DerivedCategoryModule A V) (D' : DerivedCategoryModule B V)
    (ρ : D ≅ (primeSingle A V).obj M) (ρ' : D' ≅ (primeSingle B V).obj N)
    (Φ : PrimeTensorCoefficientIso φ V D D')
    (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ)
    (t : primeTensorInputComplex φ V M C ⟶ primeTensorOutputComplex φ V N C) : Prop :=
  ∃ (ρA : D ≅ (primeLocalization A V).obj (primeSingleComplex A V M))
    (ρB : D' ≅ (primeLocalization B V).obj (primeSingleComplex B V N))
    (facZ : (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ).obj
        ((primeLocalization B V).obj C) ⟶
      (primeLocalization A V).obj
        (primeRestrictedComplex φ V C))
    (facNZ : (primeLocalization A V).obj (primeTensorOutputComplex φ V N C) ⟶
      (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ).obj
        ((primeLocalization B V).obj
          (primeSingleComplex B V N ⊗ C)))
    (μA : ((derivedTensor (ModuleCat.{u + 1} A) V).obj
        ((primeLocalization A V).obj (primeSingleComplex A V M))).obj
          ((primeLocalization A V).obj
            (primeRestrictedComplex φ V C)) ⟶
      (primeLocalization A V).obj (primeTensorInputComplex φ V M C))
    (μB : ((derivedTensor (ModuleCat.{u + 1} B) V).obj
        ((primeLocalization B V).obj (primeSingleComplex B V N))).obj
          ((primeLocalization B V).obj C) ⟶
      (primeLocalization B V).obj
        (primeSingleComplex B V N ⊗ C)),
    HEq ρA ρ ∧ HEq ρB ρ' ∧
    HEq facZ ((primeRestrictionFactors φ V).hom.app C) ∧
    HEq facNZ ((primeRestrictionFactors φ V).inv.app
      (primeSingleComplex B V N ⊗ C)) ∧
    HEq μA (Functor.LaxMonoidal.μ (primeLocalization A V) (primeSingleComplex A V M)
      (primeRestrictedComplex φ V C)) ∧
    HEq μB (Functor.LaxMonoidal.μ (primeLocalization B V)
      (primeSingleComplex B V N) C) ∧
    ((derivedTensor (ModuleCat.{u + 1} A) V).obj D).map facZ ≫
      ((derivedTensor (ModuleCat.{u + 1} A) V).map ρA.hom).app
        ((primeLocalization A V).obj
          (primeRestrictedComplex φ V C)) ≫
      μA ≫ (primeLocalization A V).map t ≫ facNZ =
    Φ.hom.app ((primeLocalization B V).obj C) ≫
      (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ).map
        (((derivedTensor (ModuleCat.{u + 1} B) V).map ρB.hom).app
          ((primeLocalization B V).obj C) ≫ μB)

end AlgebraicGeometry.Etale
