/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionNorm4

/-!
# Termwise normalization of coefficient tensor maps

Source: Stacks Project, Tags 03EK, 06YU and 0F1J, coefficient reduction
(blueprint: def-kun-prime-coefficient-termwise-normalization).

The second factor is any cochain complex, including every degree-zero sheaf.
The equation specifies the coefficient map on every total tensor summand.
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

/-- Canonical morphism on one totalization summand for coefficient reduction.
Source: Stacks, Tags 03EK, 06YU and 0F1J
(blueprint: def-kun-prime-coefficient-termwise-normalization). -/
def primeTermwiseCanonicalComponent
    (φ : A →+* B) (V : Scheme.{u})
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B))
    (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ)
    (q : M ⟶ (Sheaf.restrictScalars V.smallEtaleTopology φ).obj N)
    (i j k : ℤ) (hk : i + j = k) :=
  (primeTensorTermMap φ V M N q).f i ▷
      (Sheaf.restrictScalars V.smallEtaleTopology φ).obj
        (C.X j) ≫
    Functor.LaxMonoidal.μ (Sheaf.restrictScalars V.smallEtaleTopology φ)
      ((primeSingleComplex B V N).X i) (C.X j) ≫
    (Sheaf.restrictScalars V.smallEtaleTopology φ).map
      (HomologicalComplex.ιTensorObj (primeSingleComplex B V N)
        C i j k hk)

/-- The component of a candidate chain map after the canonical totalization
inclusion. Source: Stacks, Tags 03EK and 0F1J
(blueprint: def-kun-prime-coefficient-termwise-normalization). -/
def primeTermwiseInputComponent
    (φ : A →+* B) (V : Scheme.{u})
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B))
    (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ)
    (t : primeTensorInputComplex φ V M C ⟶
      primeTensorOutputComplex φ V N C)
    (i j k : ℤ) (hk : i + j = k) :=
  HomologicalComplex.ιTensorObj (primeSingleComplex A V M)
      (primeRestrictedComplex φ V C) i j k hk ≫ t.f k


/-- Prescribe a chain map on each total tensor summand using q in the first factor
and scalar restriction's lax tensor comparison. Thus t has the formula
x tensor y maps to q(x) tensor y, with the canonical summand inclusions included.
Source: Stacks, Tags 03EK, 06YU and 0F1J
(blueprint: def-kun-prime-coefficient-termwise-normalization). -/
def PrimeTermwiseTensorCompatibility
    (φ : A →+* B) (V : Scheme.{u})
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B))
    (C : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ)
    (q : M ⟶ (Sheaf.restrictScalars V.smallEtaleTopology φ).obj N)
    (t : primeTensorInputComplex φ V M C ⟶ primeTensorOutputComplex φ V N C) : Prop :=
  ∀ (i j k : ℤ) (hk : i + j = k),
    primeTermwiseInputComponent φ V M N C t i j k hk =
      primeTermwiseCanonicalComponent φ V M N C q i j k hk


end AlgebraicGeometry.Etale
