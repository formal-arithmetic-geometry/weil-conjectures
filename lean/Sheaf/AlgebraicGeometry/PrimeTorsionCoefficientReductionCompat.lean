/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionLocalization

/-!
# Prime coefficient tensor comparison constructions

Source: Stacks Project, Tags 03EK, 06YU and 0F1J, coefficient reduction
(blueprint: def-kun-prime-coefficient-normalization).
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
/-- Normalize the coefficient isomorphism on every cochain complex by its termwise
tensor map and localization. In particular this includes every sheaf in degree zero.
Flat first factors compute these tensors for arbitrary complexes (Step 4 of 0F1J).
Source: Stacks, Tags 03EK, 06YU and 0F1J
(blueprint: def-kun-prime-coefficient-normalization). -/
def PrimeTensorCoefficientNormalized (φ : A →+* B) (V : Scheme.{u})
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B))
    (q : M ⟶ (Sheaf.restrictScalars V.smallEtaleTopology φ).obj N)
    (D : DerivedCategoryModule A V) (D' : DerivedCategoryModule B V)
    (ρ : D ≅ (primeSingle A V).obj M) (ρ' : D' ≅ (primeSingle B V).obj N)
    (Φ : PrimeTensorCoefficientIso φ V D D') : Prop :=
  IsIso (primeCoefficientTensorMap φ V M N) ∧
    ∀ (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ),
      ∃ (t : primeTensorInputComplex φ V M C ⟶ primeTensorOutputComplex φ V N C),
        PrimeTermwiseTensorCompatibility φ V M N C q t ∧
        PrimeTensorLocalizationCompatibility φ V M N q D D' ρ ρ' Φ C t

end AlgebraicGeometry.Etale
