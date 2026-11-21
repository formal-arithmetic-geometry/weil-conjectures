/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteExceptionalInverseImage

/-!
# Cohomology with supports in the zero section

The base field is arbitrary of positive characteristic different from l.

This is the displayed Hom definition on the unbounded intrinsic pro-etale derived
category. The source object is the constant coefficient ring, placed in degree zero.
The exceptional inverse image is the published finite-coefficient comparison composite.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- Cohomology supported on the zero section of the relative affine line: morphisms
from the coefficient unit to the shifted exceptional inverse image. The coefficient
ring is the actual quotient `O_E / (pi_E^n)`, and the coefficient unit is its constant
ring sheaf regarded as a module over itself and placed in degree zero. -/
noncomputable def zeroSectionSupportedCohomology
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (K : Scheme.proEtaleDerivedCategory (PurityFiniteSetting.Line Y)
      (Padic.coefficientExtensionRing l E n)) (q : ℤ) : Type _ :=
  letI : (PurityFiniteSetting.Line Y).Over (Spec (.of k)) :=
    ⟨PurityFiniteSetting.lineProjection Y ≫ (Y ↘ Spec (.of k))⟩
  letI : LocallyOfFiniteType (PurityFiniteSetting.Line Y ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType
      ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
  letI : QuasiCompact (PurityFiniteSetting.Line Y ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact
      ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))))
  ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _) :
      Scheme.proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)) ⟶
    ((Scheme.finiteExceptionalInverseImage l E n hn k Y
      (PurityFiniteSetting.Line Y) (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj K)⟦q⟧

end WeilConjectures
