/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.PerfectProjection.PerfectProjectionFormula
public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateThickLocus
import WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleCoefficientTensorTransport
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement

/-! # Transport of projection arrows through coefficient isomorphisms

Source: Stacks Project, Cohomology on Sites, Tags 0B56 and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.Scheme.CoefficientTensorTransport

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

end AlgebraicGeometry.Scheme.CoefficientTensorTransport

namespace AlgebraicGeometry.Scheme

/-- The native derived tensor with its flat K-flat representative comparison.
Source: Stacks Tags 06YT and 0FPT. -/
@[irreducible] private def coefficientTensorModel (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) : ProEtaleTensorModel W R where
  tensor := @MonoidalCategory.tensor _ _
    (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology W) R)
  representative := NatIso.ofComponents
    (fun P ↦ RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
      (ProEt.topology W) R P.1.obj P.2.obj (Or.inl P.1.property.1))
    (fun f ↦ RingedDerivedNative.tensorIso_naturality.{u + 1, u, 0, u + 2}
      (ProEt.topology W) R _ _ _ _ _ _ f.1.hom f.2.hom)

end AlgebraicGeometry.Scheme
