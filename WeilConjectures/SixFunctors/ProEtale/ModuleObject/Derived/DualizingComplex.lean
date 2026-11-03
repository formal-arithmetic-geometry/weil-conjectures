/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit

/-! Canonical dualizing construction shared by the coefficient cases. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
/-- The dualizing object used in coefficient biduality: the published constructible
exceptional adjoint applied to the coefficient unit. Finite cohomological dimension is
supplied by the finite-or-algebraically-closed base-field alternative, without an extra
hypothesis or an ambient exceptional adjoint.
Source: latest blueprint det-pd-biduality-coefficients, delta in cases (i)--(iv), and sk-def-ops
(blueprint: def-pd-coefficient-case-dualizing-complex). -/
def coefficientCaseDualizingComplex
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hbase : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj Λ X.left)) := by
  let s : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))
  letI : LocallyOfFiniteType s.hom := by
    change LocallyOfFiniteType (𝟙 _)
    infer_instance
  letI : QuasiCompact s.hom := by
    change QuasiCompact (𝟙 _)
    infer_instance
  letI : IsSeparated s.hom := by
    change IsSeparated (𝟙 _)
    infer_instance
  exact ((ctfExceptionalInverseImage Λ ell k
    (hbase.elim (fun h ↦ @BaseFieldFiniteCD.of_finite ell _ k _ h)
      (fun h ↦ @BaseFieldFiniteCD.of_isAlgClosed ell _ k _ h))
    (Over.homMk X.hom : X ⟶ s) hΛ).obj
      ⟨𝟙_ _, condensedCoefficientUnit_mem Λ (Spec (.of k))⟩).obj

end AlgebraicGeometry.ProEtale.CondensedRing
