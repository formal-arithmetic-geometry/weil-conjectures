/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

import Sheaf.Paper.IntegralConstructibleSerre
public import Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! # Triangulation for bounded constructible integral p-adic coefficients

Source: Bhatt--Scholze, Section 6.8, Definition 6.8.10 and Proposition 6.8.11(1),(3),
as implemented by the integral constructible Serre theorem; the generic homology-property
triangulation theorem supplies the derived conclusion.
(blueprint: lem-weil-pbc-padic-integers-bounded-triangulated)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
  (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The integral coefficient ring of a finite p-adic subfield has a triangulated
bounded constructible category.

Source: Bhatt--Scholze, Section 6.8, as implemented by
`CondensedRing.integralConstructible_serre` and the conditional homology-property theorem.
Proof: equip E with the norm induced from the fixed algebraic closure. Its valuation
ring is exactly `CondensedRing.continuousIntegers`. The three integral constructible
Serre closures therefore apply to the specified coefficient ring. Apply the conditional
bounded-constructible triangulation theorem.
(blueprint: lem-weil-pbc-padic-integers-bounded-triangulated) -/
instance isTriangulated_boundedConstructible_padicIntegers :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)).IsTriangulated := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  obtain ⟨hker, hcok, hext⟩ := CondensedRing.integralConstructible_serre ℓ E.1 X
  change ObjectProperty.IsClosedUnderKernels
    (IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) at hker
  change ObjectProperty.IsClosedUnderCokernels
    (IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) at hcok
  change ObjectProperty.IsClosedUnderExtensions
    (IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) at hext
  exact isTriangulated_boundedConstructible_of_serre _

end AlgebraicGeometry.ProEtale
